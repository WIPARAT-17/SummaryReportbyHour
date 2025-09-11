import requests
import re
import html
import json
import xml.etree.ElementTree as ET
from ftfy import fix_text
import io
import csv
import datetime
import os
import argparse
import pandas as pd
from flask import Flask, request, render_template, jsonify, send_from_directory, send_file, send_from_directory
import tempfile
import threading
import uuid
from reportlab.lib.pagesizes import letter, landscape # เพิ่ม landscape เข้ามา
from reportlab.platypus import SimpleDocTemplate, Table, Paragraph, Spacer, PageBreak ,TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import inch
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
import logging
from queue import Queue
import zipfile
import shutil
import time

# สร้าง Flask application
app = Flask(__name__)

# --- สถานะการประมวลผลและ Lock สำหรับ Thread-safe ---
# `processing_status` เก็บสถานะของแต่ละงานที่กำลังประมวลผล โดยใช้ job_id เป็น key
# ตัวอย่าง:
# {
#     'job_id_1': {'total': 100, 'processed': 10, 'completed': False, 'error': None, 'canceled': False, 'results': [], 'temp_dir': '/tmp/report_job_xyz', 'zip_file_path': None, 'timestamp': datetime_obj},
#     'job_id_2': {...}
# }
processing_status = {}
# `status_lock` ใช้สำหรับควบคุมการเข้าถึง `processing_status` เพื่อป้องกัน Race Condition ใน Multi-threading
status_lock = threading.Lock()

# --- ตั้งค่า Logger และ Log Queue ---
# `log_queue` ใช้เก็บข้อความ log ที่จะถูกส่งไปยังหน้าเว็บแบบ Real-time
log_queue = Queue()

# ตั้งค่า logger สำหรับการบันทึกข้อความ (เช่น INFO, WARNING, ERROR)
logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO) # กำหนดระดับ log ขั้นต่ำที่จะแสดง

UPLOAD_FOLDER = 'uploads'
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER

# ล้าง handler เก่าที่อาจมีอยู่ เพื่อป้องกัน log ซ้ำ
if logger.handlers:
    for handler in list(logger.handlers):
        logger.removeHandler(handler)

# Custom Log Handler ที่ส่งข้อความ log ไปยัง Queue
class QueueHandler(logging.Handler):
    def __init__(self, queue):
        super().__init__()
        self.queue = queue

    def emit(self, record):
        try:
            msg = self.format(record) # จัดรูปแบบข้อความ log

            # ตรวจสอบและกรองข้อความที่ไม่ต้องการออกไปยังหน้าเว็บ
            if "📁 ลบโฟลเดอร์ CSV/PDF ชั่วคราว" in msg:
                return # ไม่ใส่ข้อความนี้ลงในคิว

            # ใช้ Regular Expression เพื่อดึงเฉพาะส่วนข้อความหลักของ log (ไม่เอา timestamp, level, job_id)
            log_pattern = re.compile(r"^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2},\d{3} - (INFO|WARNING|ERROR|CRITICAL) - (Job [0-9a-f-]+: )?(.*)")
            match = log_pattern.match(msg)
            if match:
                clean_msg = match.group(3) # ดึงส่วนข้อความหลัก
                self.queue.put(clean_msg) # ใส่ข้อความที่กรองแล้วลงในคิว
            else:
                self.queue.put(msg) # ถ้าไม่ตรง pattern ก็ใส่ข้อความเต็มลงไป

        except Exception:
            self.handleError(record) # จัดการข้อผิดพลาดที่เกิดขึ้นใน handler นี้

# ตั้งค่า Console Handler เพื่อให้ log แสดงใน Console/Terminal ด้วย
console_handler = logging.StreamHandler()
console_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
logger.addHandler(console_handler)

# เพิ่ม QueueHandler เข้าไปใน logger เพื่อให้ log ไปอยู่ใน Queue ด้วย
queue_handler = QueueHandler(log_queue)
logger.addHandler(queue_handler)

# --- ตั้งค่าฟอนต์ภาษาไทยสำหรับ PDF ---
THAI_FONT_NAME = 'THSarabunNew' # ชื่อฟอนต์ที่จะใช้ใน ReportLab
THAI_FONT_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'THSarabunNew.ttf') # Path ไปยังไฟล์ฟอนต์

THAI_FONT_REGISTERED = False
# ตรวจสอบว่าไฟล์ฟอนต์มีอยู่หรือไม่
if os.path.exists(THAI_FONT_PATH):
    try:
        # ลงทะเบียนฟอนต์กับ ReportLab เพื่อให้สามารถใช้งานใน PDF ได้
        pdfmetrics.registerFont(TTFont(THAI_FONT_NAME, THAI_FONT_PATH))
        THAI_FONT_REGISTERED = True
        #logger.info(f"Thai font '{THAI_FONT_NAME}' registered successfully from '{THAI_FONT_PATH}'.")
    except Exception as e:
        logger.error(f"ERROR: Could not register Thai font '{THAI_FONT_NAME}'. Error: {e}")
else:
    logger.warning(f"WARNING: Thai font file '{THAI_FONT_PATH}' not found. Please ensure the font file is in the same directory as the script.")

# --- ฟังก์ชันสำหรับประมวลผลข้อมูล ---
def get_data_from_api(nod_id, itf_id, job_id):
    """
    ดึงข้อมูลสถานะวงจรจาก API ภายนอก (SOAP-based) และแปลงเป็น JSON

    Parameters:
    - nod_id (str): Node ID ของอุปกรณ์
    - itf_id (str): Interface ID ของ Interface
    - job_id (str): ID ของงานปัจจุบันสำหรับ logging

    Returns:
    - dict: ข้อมูล JSON ที่ได้จาก API หรือ None หากเกิดข้อผิดพลาด
    """
     # 1. เปลี่ยน URL ของ API เป็นเวอร์ชัน v2
    url = "http://1.179.233.116:8082/api_csoc_02/server_solarwinds_ginv2.php"

    headers = {
        # 2. เปลี่ยน SOAPAction ให้ตรงกับ URL ใหม่
        "SOAPAction": "http://1.179.233.116/api_csoc_02/server_solarwinds_ginv2.php/circuitStatus",
        "Content-Type": "text/xml; charset=utf-8",
    }
    # 3. เปลี่ยน Namespace (xmlns) ใน SOAP Body เป็นเวอร์ชัน v2
    body = f"""<?xml version="1.0" encoding="utf-8"?>
<soap:Envelope xmlns:soap="http://schemas.xmlsoap.org/soap/envelope/"
               xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
               xmlns:xsd="http://www.w3.org/2001/XMLSchema">
  <soap:Body>
    <circuitStatus xmlns="http://1.179.233.116/soap/#Service_Solarwinds_ginv2">
      <nodID>{nod_id}</nodID>
      <itfID>{itf_id}</itfID>
    </circuitStatus>
  </soap:Body>
</soap:Envelope>"""

    # -------------------- END: ส่วนที่แก้ไข --------------------

    try:
        # ส่ง POST Request ไปยัง API ด้วยข้อมูล SOAP Body และ Headers
        resp = requests.post(url, data=body, headers=headers, timeout=10)
        resp.raise_for_status() # ตรวจสอบว่า Request สำเร็จหรือไม่ (HTTP 2xx)

        # ค้นหา XML Response ที่ถูกต้องภายในข้อความตอบกลับ
        match = re.search(r"(<\?xml.*?</SOAP-ENV:Envelope>)", resp.text, re.DOTALL)
        if not match:
            logger.warning(f"ไม่พบ XML Response สำหรับ NodeID: {nod_id}, Interface ID: {itf_id}")
            return None

        # Parse XML Response เพื่อดึงข้อมูลส่วน 'return'
        root = ET.fromstring(match.group(1))
        return_tag = root.find(".//{*}return")
        if return_tag is None or not return_tag.text:
            logger.warning(f"API ไม่มีข้อมูลตอบกลับสำหรับ NodeID: {nod_id}, Interface ID: {itf_id}")
            return None

        raw_text = return_tag.text
        # Unescape HTML entities (e.g., &quot; becomes ")
        html_unescaped = html.unescape(raw_text)
        # Fix encoding issues that might arise from unicode escape sequences
        fixed_text = fix_text(bytes(html_unescaped, "utf-8").decode("unicode_escape"))
        parsed_json = json.loads(fixed_text) # แปลง String JSON เป็น Python Dictionary/List
        return parsed_json
    except requests.exceptions.RequestException as req_e:
        logger.error(f"❌ ดึงข้อมูล NodeID: {nod_id}, Interface ID: {itf_id} ล้มเหลว: {req_e}")
        return None
    except ET.ParseError as parse_e:
        logger.error(f"❌ XML Parsing ผิดพลาดสำหรับ NodeID: {nod_id}, Interface ID: {itf_id}: {parse_e}")
        return None
    except json.JSONDecodeError as json_e:
        logger.error(f"❌ JSON Decoding ผิดพลาดสำหรับ NodeID: {nod_id}, Interface ID: {itf_id}: {json_e}")
        return None
    except Exception as e:
        logger.error(f"❌ ข้อผิดพลาดไม่คาดคิดสำหรับ NodeID: {nod_id}, Interface ID: {itf_id}: {e}")
        return None

def process_json_data(raw_json_data, job_id, excel_node_id, excel_agency_name):
    """
    ประมวลผลข้อมูล JSON ที่ได้จาก API เพื่อเตรียมสำหรับสร้างไฟล์ CSV/PDF
    - เติมข้อมูลให้ครบ 24 ชั่วโมงในแต่ละวันของช่วงเวลาที่มีข้อมูล
    - คำนวณค่าเฉลี่ยรวม (Grand Total Average) ของ In_Averagebps และ Out_Averagebps
    - จัดรูปแบบ Bandwidth และปริมาณการใช้งาน

    Parameters:
    - raw_json_data (list or dict): ข้อมูล JSON ดิบจาก API
    - job_id (str): ID ของงานปัจจุบันสำหรับ logging
    - excel_node_id (str): Node ID จากไฟล์ Excel (ใช้เป็นค่าเริ่มต้นหาก API ไม่มี Customer_Curcuit_ID)
    - excel_agency_name (str): ชื่อหน่วยงานจากไฟล์ Excel (ใช้เป็นค่าเริ่มต้นหาก API ไม่มี Address)

    Returns:
    - tuple: (headers, processed_data, grand_total_row)
        - headers (list): รายชื่อหัวข้อคอลัมน์ภาษาไทยที่ใช้ใน CSV/PDF
        - processed_data (list): ข้อมูลที่ประมวลผลแล้วพร้อมสำหรับตาราง (รวม 24 ชั่วโมง)
        - grand_total_row (dict): แถว Grand Total (Average)
    """
    # ------------------- START: ส่วนที่แก้ไข -------------------

    # 1. อัปเดต key ของ "วันที่และเวลา" ให้ตรงกับ API ใหม่ คือ 'Timestamp'
    column_mapping = {
        "รหัสหน่วยงาน": "Customer_Curcuit_ID",
        "ชื่อหน่วยงาน": "Address",
        "วันที่และเวลา": "Timestamp", # <--- เปลี่ยนจาก 'Timestamp'
        "ขนาดBandwidth (หน่วย Mbps)": "Bandwidth",
        "In_Averagebps": "In_Averagebps",
        "Out_Averagebps": "Out_Averagebps"
    }
    # -------------------- END: ส่วนที่แก้ไข --------------------

    desired_headers_th = list(column_mapping.keys())

    if raw_json_data is None or (isinstance(raw_json_data, list) and not raw_json_data):
        logger.warning(f"ไม่มีข้อมูล JSON ให้ประมวลผลสำหรับ Job {job_id}")
        return desired_headers_th, [], {}

    data_to_process = raw_json_data if isinstance(raw_json_data, list) else [raw_json_data]

    api_customer_circuit_id = excel_node_id
    address_to_use = excel_agency_name
    bandwidth_to_use = ''

    first_item = data_to_process[0]

    api_customer_circuit_id = first_item.get(column_mapping["รหัสหน่วยงาน"]) or excel_node_id
    api_address = first_item.get(column_mapping["ชื่อหน่วยงาน"]) or excel_agency_name
    bandwidth_raw_from_api = first_item.get(column_mapping["ขนาดBandwidth (หน่วย Mbps)"]) or ''

    if "FTTx" in str(bandwidth_raw_from_api):
        bandwidth_to_use = "20 Mbps."
    else:
        try:
            numeric_value_match = re.search(r'[\d.]+', str(bandwidth_raw_from_api))
            if numeric_value_match:
                numeric_value = float(numeric_value_match.group())
                bandwidth_to_use = f"{int(numeric_value)} Mbps."
            else:
                bandwidth_to_use = str(bandwidth_raw_from_api)
        except (ValueError, TypeError, AttributeError):
            bandwidth_to_use = str(bandwidth_raw_from_api)

    min_date_from_api = None
    max_date_from_api = None

    # ------------------- START: ส่วนที่แก้ไข -------------------
    # 2. ปรับ logic การอ่านค่าเวลาให้รับค่าจาก 'Timestamp' ที่เป็น string โดยตรง
    for item in data_to_process:
        timestamp_str = item.get('Timestamp')
        # ตรวจสอบว่า Timestamp ไม่ใช่ค่าว่าง
        if timestamp_str:
            try:
                # ลองแปลงค่าเวลาโดยคาดว่ามีรูปแบบเป็น 'YYYY-MM-DD HH:MM:SS'
                # หาก API ส่งรูปแบบอื่นมา อาจจะต้องปรับ format string ('%d/%m/%Y %H') ตรงนี้
                dt_obj_from_api = datetime.datetime.strptime(timestamp_str, '%d/%m/%Y %H')
                if min_date_from_api is None or dt_obj_from_api.date() < min_date_from_api:
                    min_date_from_api = dt_obj_from_api.date()
                if max_date_from_api is None or dt_obj_from_api.date() > max_date_from_api:
                    max_date_from_api = dt_obj_from_api.date()
            except (ValueError, TypeError):
                logger.warning(f"Job {job_id}: ไม่สามารถแปลงวันที่จาก Timestamp ได้: '{timestamp_str}'")
                continue
    # -------------------- END: ส่วนที่แก้ไข --------------------

    if min_date_from_api is None or max_date_from_api is None:
        logger.warning(f"Job {job_id}: ไม่พบข้อมูลเวลาที่ถูกต้องจาก API เลย จะใช้เดือนปัจจุบันเป็นค่าเริ่มต้น")
        today = datetime.date.today()
        first_day_of_current_month = today.replace(day=1)
        report_end_date = first_day_of_current_month - datetime.timedelta(days=1)
        report_start_date = report_end_date.replace(day=1)
    else:
        report_start_date = min_date_from_api.replace(day=1)
        next_month_start_for_max = (max_date_from_api.replace(day=1) + datetime.timedelta(days=32)).replace(day=1)
        report_end_date = next_month_start_for_max - datetime.timedelta(days=1)

    full_data_structure = {}
    current_date = report_start_date
    while current_date <= report_end_date:
        for hour in range(24):
            dt_obj = datetime.datetime.combine(current_date, datetime.time(hour, 0, 0))
            formatted_date_time = dt_obj.strftime('%Y-%m-%d %H.%M.%S')
            date_key = current_date.strftime('%Y-%m-%d')

            if date_key not in full_data_structure:
                full_data_structure[date_key] = {}

            full_data_structure[date_key][formatted_date_time] = {
                "รหัสหน่วยงาน": api_customer_circuit_id,
                "ชื่อหน่วยงาน": api_address,
                "วันที่และเวลา": formatted_date_time,
                "ขนาดBandwidth (หน่วย Mbps)": bandwidth_to_use,
                "In_Averagebps": "0",
                "Out_Averagebps": "0",
                "_raw_incoming": 0,
                "_raw_outcoming": 0
            }
        current_date += datetime.timedelta(days=1)

    # ------------------- START: ส่วนที่แก้ไข -------------------
    # 3. ปรับ logic การอัปเดตข้อมูลให้ดึงค่าเวลาจาก 'Timestamp' เช่นกัน
    for item in data_to_process:
        dt_obj_from_api = None
        timestamp_str = item.get('Timestamp')
        if timestamp_str:
            try:
                dt_obj_from_api = datetime.datetime.strptime(timestamp_str, '%d/%m/%Y %H')
            except (ValueError, TypeError):
                continue

        if dt_obj_from_api:
            # ใช้ dt_obj_from_api ที่ได้มาในการอัปเดตข้อมูลต่อไป...
            # (โค้ดส่วนที่เหลือในลูปนี้เหมือนเดิม ไม่ต้องแก้ไข)
    # -------------------- END: ส่วนที่แก้ไข --------------------
            date_key = dt_obj_from_api.strftime('%Y-%m-%d')
            # ปรับ format ของเวลาให้เป็น H.M.S เพื่อให้ตรงกับ key ที่สร้างไว้
            formatted_time_from_api = dt_obj_from_api.strftime('%Y-%m-%d %H.%M.%S')


            if date_key in full_data_structure and formatted_time_from_api in full_data_structure[date_key]:
                item_customer_id = item.get(column_mapping["รหัสหน่วยงาน"])
                item_address = item.get(column_mapping["ชื่อหน่วยงาน"])

                if item_customer_id:
                    full_data_structure[date_key][formatted_time_from_api]["รหัสหน่วยงาน"] = item_customer_id

                if item_address:
                    full_data_structure[date_key][formatted_time_from_api]["ชื่อหน่วยงาน"] = item_address

                in_avg_bps = item.get('In_Averagebps', '0')
                out_avg_bps = item.get('Out_Averagebps', '0')

                try:
                    in_avg_bps_float = float(in_avg_bps)
                    full_data_structure[date_key][formatted_time_from_api]["_raw_incoming"] = int(in_avg_bps_float)
                    full_data_structure[date_key][formatted_time_from_api]["In_Averagebps"] = f"{int(in_avg_bps_float):,}"
                except (ValueError, TypeError):
                    full_data_structure[date_key][formatted_time_from_api]["_raw_incoming"] = 0
                    full_data_structure[date_key][formatted_time_from_api]["In_Averagebps"] = str(in_avg_bps)

                try:
                    out_avg_bps_float = float(out_avg_bps)
                    full_data_structure[date_key][formatted_time_from_api]["_raw_outcoming"] = int(out_avg_bps_float)
                    full_data_structure[date_key][formatted_time_from_api]["Out_Averagebps"] = f"{int(out_avg_bps_float):,}"
                except (ValueError, TypeError):
                    full_data_structure[date_key][formatted_time_from_api]["_raw_outcoming"] = 0
                    full_data_structure[date_key][formatted_time_from_api]["Out_Averagebps"] = str(out_avg_bps)

                item_bandwidth_raw = item.get(column_mapping["ขนาดBandwidth (หน่วย Mbps)"])
                if item_bandwidth_raw:
                    if "FTTx" in str(item_bandwidth_raw):
                        full_data_structure[date_key][formatted_time_from_api]["ขนาดBandwidth (หน่วย Mbps)"] = "20 Mbps."
                    else:
                        try:
                            numeric_value_match = re.search(r'[\d.]+', str(item_bandwidth_raw))
                            if numeric_value_match:
                                numeric_value = float(numeric_value_match.group())
                                full_data_structure[date_key][formatted_time_from_api]["ขนาดBandwidth (หน่วย Mbps)"] = f"{int(numeric_value)} Mbps."
                            else:
                                full_data_structure[date_key][formatted_time_from_api]["ขนาดBandwidth (หน่วย Mbps)"] = str(item_bandwidth_raw)
                        except (ValueError, TypeError, AttributeError):
                            full_data_structure[date_key][formatted_time_from_api]["ขนาดBandwidth (หน่วย Mbps)"] = str(item_bandwidth_raw)

    processed_data = []
    total_incoming_sum = 0
    total_outcoming_sum = 0
    data_points_count = 0

    for date_key in sorted(full_data_structure.keys()):
        for time_key in sorted(full_data_structure[date_key].keys()):
            row = full_data_structure[date_key][time_key]
            processed_data.append(row)
            total_incoming_sum += row.get("_raw_incoming", 0)
            total_outcoming_sum += row.get("_raw_outcoming", 0)
            data_points_count += 1

    average_incoming = 0
    average_outcoming = 0
    if data_points_count > 0:
        average_incoming = round(total_incoming_sum / data_points_count)
        average_outcoming = round(total_outcoming_sum / data_points_count)

    grand_total_row = {
        "รหัสหน่วยงาน": "Grand Total",
        "ชื่อหน่วยงาน": "",
        "วันที่และเวลา": "",
        "ขนาดBandwidth (หน่วย Mbps)": "",
        "In_Averagebps": f"{average_incoming:,}",
        "Out_Averagebps": f"{average_outcoming:,}"
    }

    return desired_headers_th, processed_data, grand_total_row



def export_to_csv(headers, data, filename, job_id, node_name):
    """
    สร้างและบันทึกไฟล์ CSV
    Parameters:
    - headers (list): รายชื่อหัวข้อคอลัมน์
    - data (list): ข้อมูลที่จะเขียนลง CSV (รวม Grand Total แล้ว)
    - filename (str): ชื่อไฟล์ CSV ที่จะบันทึก
    - job_id (str): ID ของงาน (สำหรับ logging)
    - node_name (str): ชื่อ Node (สำหรับ logging)
    Returns:
    - tuple: (bool, str) -> (True หากสำเร็จ, ข้อความสถานะ)
    """
    try:
        # เปิดไฟล์ในโหมด 'w' (write), 'newline=''' เพื่อป้องกันบรรทัดว่าง, 'utf-8-sig' สำหรับ BOM (Byte Order Mark)
        # เพื่อให้ Excel เปิดภาษาไทยได้ถูกต้อง
        with open(filename, 'w', newline='', encoding='utf-8-sig') as f:
            cw = csv.writer(f) # สร้าง CSV writer object
            if headers and data:
                cw.writerow(headers) # เขียนหัวข้อคอลัมน์
                # ไม่จำเป็นต้องเก็บ last_customer_id/name สำหรับ CSV เพราะจะแสดงทุกแถว
                for row in data:
                    new_row = [
                        row.get('รหัสหน่วยงาน', ''),
                        row.get('ชื่อหน่วยงาน', ''),
                        row.get('วันที่และเวลา', ''),
                        row.get('ขนาดBandwidth (หน่วย Mbps)', ''),
                        row.get('In_Averagebps', ''),
                        row.get('Out_Averagebps', '')
                    ]
                    cw.writerow(new_row) # เขียนข้อมูลแต่ละแถว
            else:
                cw.writerow(["No Data"]) # กรณีไม่มีข้อมูล
        logger.info(f"✅ สร้าง CSV สำหรับ '{node_name}' สำเร็จแล้ว")
        return True, "Success"
    except Exception as e:
        logger.error(f"❌ สร้าง CSV สำหรับ '{node_name}' ล้มเหลว: {e}")
        return False, str(e)

def export_to_pdf(headers, daily_data, grand_total_row, filename, job_id, node_name):
    """
    สร้างและบันทึกไฟล์ PDF โดยให้แต่ละวันขึ้นหน้าใหม่, Grand Total อยู่ต่อท้ายวันสุดท้าย
    ข้อมูล "รหัสหน่วยงาน" และ "ชื่อหน่วยงาน" จะแสดงเพียงครั้งเดียวต่อวัน (ถ้าซ้ำ)
    Parameters:
    - headers (list): รายชื่อหัวข้อคอลัมน์
    - daily_data (list): ข้อมูลรายวันที่จะเขียนลง PDF (ไม่รวม Grand Total)
    - grand_total_row (dict): แถว Grand Total (Average)
    - filename (str): ชื่อไฟล์ PDF ที่จะบันทึก
    - job_id (str): ID ของงาน (สำหรับ logging)
    - node_name (str): ชื่อ Node (สำหรับ logging)
    Returns:
    - tuple: (True หากสำเร็จ, ข้อความสถานะ)
    """
    try:
        # กำหนดขนาดขอบกระดาษที่คุณต้องการ (ในหน่วย inch)
        margin_size = 0.5 * inch  # ตัวอย่าง: ขอบ 0.5 นิ้ว ทุกด้าน

        doc = SimpleDocTemplate(
            filename,
            pagesize=letter,
            leftMargin=margin_size,
            rightMargin=margin_size,
            topMargin=margin_size,
            bottomMargin=margin_size
        ) # สร้างเอกสาร PDF, กำหนดขนาดหน้าเป็น Letter และขอบกระดาษ

        styles = getSampleStyleSheet()
        elements = []

        # สร้าง ParagraphStyle สำหรับข้อความในเซลล์
        cell_paragraph_style = ParagraphStyle('TableCellParagraph', parent=styles['Normal'])
        if THAI_FONT_REGISTERED:
            cell_paragraph_style.fontName = THAI_FONT_NAME
        cell_paragraph_style.fontSize = 10
        cell_paragraph_style.alignment = 1 # จัดกึ่งกลาง (หรือ LEFT/RIGHT ตามต้องการ)


        if headers and daily_data:
            data_by_date = {}
            for row in daily_data:
                date_time_str = row.get('วันที่และเวลา', '')
                try:
                    date_key = datetime.datetime.strptime(date_time_str, '%Y-%m-%d %H.%M.%S').strftime('%Y-%m-%d')
                except ValueError:
                    date_key = 'Uncategorized'
                    logger.warning(f"Found uncategorized date for PDF: {date_time_str}")
                if date_key not in data_by_date:
                    data_by_date[date_key] = []
                data_by_date[date_key].append(row)

            report_month_str = "ไม่ระบุเดือน"
            if data_by_date:
                first_date_str = sorted(data_by_date.keys())[0]
                try:
                    first_date_obj = datetime.datetime.strptime(first_date_str, '%Y-%m-%d')
                    thai_months = {
                        1: "มกราคม", 2: "กุมภาพันธ์", 3: "มีนาคม", 4: "เมษายน",
                        5: "พฤษภาคม", 6: "มิถุนายน", 7: "กรกฎาคม", 8: "สิงหาคม",
                        9: "กันยายน", 10: "ตุลาคม", 11: "พฤศจิกายน", 12: "ธันวาคม"
                    }
                    report_month_str = thai_months.get(first_date_obj.month, "ไม่ระบุเดือน")
                except ValueError:
                    logger.warning(f"Could not parse first date for month determination: {first_date_str}")

            first_page = True
            sorted_dates = sorted(data_by_date.keys())

            # คำนวณความกว้างที่ใช้ได้สำหรับตาราง
            # letter width = 8.5 inches
            # Usable width = page_width - leftMargin - rightMargin
            # letter page: 8.5 * inch
            usable_page_width = letter[0] - (2 * margin_size) # letter[0] คือความกว้างของหน้ากระดาษ

            for i, date_key in enumerate(sorted_dates):
                group_data = data_by_date[date_key]

                if not first_page:
                    elements.append(PageBreak())

                title_style = styles['Title']
                if THAI_FONT_REGISTERED:
                    title_style.fontName = THAI_FONT_NAME
                title_style.fontSize = 20
                title_style.alignment = 1
                elements.append(Paragraph("Customer Interface Summary Report by Hour", title_style))
                elements.append(Spacer(1, 0.2 * inch))

                month_report_style = ParagraphStyle('MonthReport', parent=styles['Normal'])
                if THAI_FONT_REGISTERED:
                    month_report_style.fontName = THAI_FONT_NAME
                month_report_style.fontSize = 18
                month_report_style.alignment = 1
                elements.append(Paragraph(f"รายงานประจำเดือน {report_month_str}", month_report_style))
                elements.append(Spacer(1, 0.2 * inch))

                date_header_style = ParagraphStyle('DateHeader', parent=styles['Normal'])
                if THAI_FONT_REGISTERED:
                    date_header_style.fontName = THAI_FONT_NAME
                date_header_style.fontSize = 16
                date_header_style.alignment = 1
                elements.append(Paragraph(f"<b>วันที่ </b> {date_key}", date_header_style))
                elements.append(Spacer(1, 0.2 * inch))

                table_headers = [
                    "รหัสหน่วยงาน",
                    "ชื่อหน่วยงาน",
                    "วันที่และเวลา",
                    "ขนาดBandwidth (หน่วย Mbps)",
                    "ปริมาณการใช้งาน incoming (หน่วย bps)",
                    "ปริมาณการใช้งาน outcoming (หน่วย bps)"
                ]
                
                # *** สำคัญ: กำหนดความกว้างคอลัมน์ (colWidths) ***
                # ต้องให้ผลรวมของคอลัมน์ไม่เกินความกว้างที่ใช้ได้ (usable_page_width)
                # ปรับสัดส่วนให้เหมาะสมกับข้อมูลของคุณ
                col_widths = [
                    0.10 * usable_page_width, # รหัสหน่วยงาน (10% ของความกว้างที่ใช้ได้)
                    0.25 * usable_page_width, # ชื่อหน่วยงาน (25% ของความกว้างที่ใช้ได้)
                    0.15 * usable_page_width, # วันที่และเวลา
                    0.15 * usable_page_width, # ขนาดBandwidth
                    0.175 * usable_page_width, # incoming
                    0.175 * usable_page_width  # outcoming
                ]
                # ตรวจสอบให้แน่ใจว่าผลรวมของเปอร์เซ็นต์เท่ากับ 1.0 (หรือ 100%)
                # เช่น 0.10 + 0.25 + 0.15 + 0.15 + 0.175 + 0.175 = 1.0

                # สร้าง header row ด้วย Paragraph Objects เพื่อให้ใช้ฟอนต์ไทยได้
                header_row_with_paragraphs = []
                header_paragraph_style = ParagraphStyle('TableHeaderParagraph', parent=styles['Normal'])
                if THAI_FONT_REGISTERED:
                    header_paragraph_style.fontName = THAI_FONT_NAME
                header_paragraph_style.fontSize = 10
                header_paragraph_style.alignment = 1 # จัดกึ่งกลางหัวตาราง
                header_paragraph_style.fontName = THAI_FONT_NAME if THAI_FONT_REGISTERED else 'Helvetica-Bold'

                for header_text in table_headers:
                    header_row_with_paragraphs.append(Paragraph(header_text, header_paragraph_style))

                table_data = [header_row_with_paragraphs]
                
                # Track rows for spanning
                span_data = {
                    'รหัสหน่วยงาน': {'start_row': -1, 'value': None},
                    'ชื่อหน่วยงาน': {'start_row': -1, 'value': None}
                }
                
                # List to store ReportLab table style commands
                table_styles_commands = []

                for idx_row, row in enumerate(group_data):
                    current_customer_id = row.get('รหัสหน่วยงาน', '')
                    current_customer_name = row.get('ชื่อหน่วยงาน', '')
                    current_bandwidth = row.get('ขนาดBandwidth (หน่วย Mbps)', '')

                    cell_data_row = [
                        Paragraph(current_customer_id, cell_paragraph_style),
                        Paragraph(current_customer_name, cell_paragraph_style),
                        Paragraph(row.get('วันที่และเวลา', ''), cell_paragraph_style),
                        Paragraph(str(current_bandwidth), cell_paragraph_style),
                        Paragraph(str(row.get('In_Averagebps', '')), cell_paragraph_style),
                        Paragraph(str(row.get('Out_Averagebps', '')), cell_paragraph_style)
                    ]
                    table_data.append(cell_data_row)

                    # Calculate actual row index in the table (offset by 1 for header row)
                    current_table_row_index = idx_row + 1 

                    # Logic for spanning "รหัสหน่วยงาน" (Column 0)
                    if span_data['รหัสหน่วยงาน']['value'] is None:
                        span_data['รหัสหน่วยงาน']['value'] = current_customer_id
                        span_data['รหัสหน่วยงาน']['start_row'] = current_table_row_index
                    elif current_customer_id != span_data['รหัสหน่วยงาน']['value']:
                        if current_table_row_index - 1 > span_data['รหัสหน่วยงาน']['start_row']:
                            table_styles_commands.append(('SPAN', (0, span_data['รหัสหน่วยงาน']['start_row']), (0, current_table_row_index - 1)))
                        span_data['รหัสหน่วยงาน']['value'] = current_customer_id
                        span_data['รหัสหน่วยงาน']['start_row'] = current_table_row_index
                    
                    # Logic for spanning "ชื่อหน่วยงาน" (Column 1)
                    if span_data['ชื่อหน่วยงาน']['value'] is None:
                        span_data['ชื่อหน่วยงาน']['value'] = current_customer_name
                        span_data['ชื่อหน่วยงาน']['start_row'] = current_table_row_index
                    elif current_customer_name != span_data['ชื่อหน่วยงาน']['value']:
                        if current_table_row_index - 1 > span_data['ชื่อหน่วยงาน']['start_row']:
                            table_styles_commands.append(('SPAN', (1, span_data['ชื่อหน่วยงาน']['start_row']), (1, current_table_row_index - 1)))
                        span_data['ชื่อหน่วยงาน']['value'] = current_customer_name
                        span_data['ชื่อหน่วยงาน']['start_row'] = current_table_row_index

                # After iterating through all rows for the current day, close any open spans
                if span_data['รหัสหน่วยงาน']['start_row'] != -1 and len(group_data) + 1 > span_data['รหัสหน่วยงาน']['start_row']:
                    table_styles_commands.append(('SPAN', (0, span_data['รหัสหน่วยงาน']['start_row']), (0, len(group_data))))
                if span_data['ชื่อหน่วยงาน']['start_row'] != -1 and len(group_data) + 1 > span_data['ชื่อหน่วยงาน']['start_row']:
                    table_styles_commands.append(('SPAN', (1, span_data['ชื่อหน่วยงาน']['start_row']), (1, len(group_data))))

                # If it's the last day and there's a Grand Total row, add it to the table data
                if i == len(sorted_dates) - 1 and grand_total_row:
                    grand_total_row_data = [
                        Paragraph(grand_total_row.get('รหัสหน่วยงาน', ''), cell_paragraph_style),
                        Paragraph(grand_total_row.get('ชื่อหน่วยงาน', ''), cell_paragraph_style),
                        Paragraph(grand_total_row.get('วันที่และเวลา', ''), cell_paragraph_style),
                        Paragraph(str(grand_total_row.get('ขนาดBandwidth (หน่วย Mbps)', '')), cell_paragraph_style),
                        Paragraph(str(grand_total_row.get('In_Averagebps', '')), cell_paragraph_style),
                        Paragraph(str(grand_total_row.get('Out_Averagebps', '')), cell_paragraph_style)
                    ]
                    table_data.append(grand_total_row_data)

                table = Table(table_data, colWidths=col_widths)
                table_style = [
                    ('BACKGROUND', (0, 0), (-1, 0), '#cccccc'),
                    ('TEXTCOLOR', (0, 0), (-1, 0), '#000000'),
                    ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
                    ('BOTTOMPADDING', (0, 0), (-1, 0), 12),
                    ('BACKGROUND', (0, 1), (-1, -1), "#ffffff"),
                    ('GRID', (0, 0), (-1, -1), 1, '#999999'),
                    ('FONTSIZE', (0, 0), (-1, -1), 10), # Font size is now largely controlled by ParagraphStyle
                    ('LEFTPADDING', (0,0), (-1,-1), 6),
                    ('RIGHTPADDING', (0,0), (-1,-1), 6),
                    ('VALIGN', (0,0), (-1,-1), 'TOP'),
                ]

                if THAI_FONT_REGISTERED:
                    table_style.append(('FONTNAME', (0, 0), (-1, 0), THAI_FONT_NAME))
                else:
                    table_style.append(('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'))

                table_style.extend(table_styles_commands)

                if i == len(sorted_dates) - 1 and grand_total_row:
                    grand_total_row_index = len(table_data) - 1
                    table_style.append(('BACKGROUND', (0, grand_total_row_index), (-1, grand_total_row_index), '#dddddd'))
                    table_style.append(('FONTNAME', (0, grand_total_row_index), (-1, grand_total_row_index), THAI_FONT_NAME if THAI_FONT_REGISTERED else 'Helvetica-Bold'))
                    table_style.append(('SPAN', (0, grand_total_row_index), (3, grand_total_row_index)))
                    table_style.append(('ALIGN', (0, grand_total_row_index), (3, grand_total_row_index), 'LEFT'))
                    table_style.append(('VALIGN', (0, grand_total_row_index), (-1, grand_total_row_index), 'MIDDLE'))

                table.setStyle(TableStyle(table_style))
                elements.append(table)
                elements.append(Spacer(1, 0.5 * inch))

                first_page = False

        else:
            no_data_style = styles['Normal']
            if THAI_FONT_REGISTERED:
                no_data_style.fontName = THAI_FONT_NAME
            elements.append(Paragraph("No circuit status data available.", no_data_style))

        doc.build(elements)
        logger.info(f"✅ สร้าง PDF สำหรับ '{node_name}' สำเร็จแล้ว")
        return True, "PDF generated successfully."
    except Exception as e:
        logger.error(f"❌ สร้าง PDF สำหรับ '{node_name}' ล้มเหลว: {e}")
        return False, f"Error generating PDF: {e}"


def process_file_in_background(file_stream, job_id):
    """
    ฟังก์ชันนี้จะทำงานในอีก Thread หนึ่ง (background process)
    โดยจะรับ file_stream (ข้อมูลไฟล์ Excel) และ job_id มาประมวลผล
    อ่านไฟล์ Excel, ดึงข้อมูลจาก API, ประมวลผล, และสร้างไฟล์ CSV/PDF
    จากนั้นจะ Zip ไฟล์ทั้งหมดและอัปเดตสถานะของงาน
    """
    temp_dir = None # ตัวแปรสำหรับเก็บ path ของโฟลเดอร์ชั่วคราว
    try:
        df = pd.read_excel(file_stream) # อ่านไฟล์ Excel ด้วย Pandas
        total_rows = len(df) # จำนวนแถวทั้งหมดใน Excel

        # อัปเดตสถานะงาน (thread-safe)
        with status_lock:
            processing_status[job_id]['total'] = total_rows
            processing_status[job_id]['results'] = [] # เก็บผลลัพธ์ของแต่ละ Node/Interface
            temp_dir = tempfile.mkdtemp(prefix=f"report_job_{job_id}_") # สร้างโฟลเดอร์ชั่วคราว
            processing_status[job_id]['temp_dir'] = temp_dir # เก็บ path โฟลเดอร์ชั่วคราวไว้ในสถานะงาน

        logger.info(f"📊 เริ่มประมวลผลไฟล์ Excel มีทั้งหมด {total_rows} รายการ")

        # ตรวจสอบว่าคอลัมน์ที่จำเป็นมีครบถ้วนใน Excel หรือไม่
        required_columns = ['NodeID', 'Interface ID', 'กระทรวง / สังกัด', 'กรม / สังกัด', 'จังหวัด', 'ชื่อหน่วยงาน', 'Node Name']
        if not all(col in df.columns for col in required_columns):
            missing_cols = [c for c in required_columns if c not in df.columns]
            with status_lock:
                processing_status[job_id]['error'] = f"ไฟล์ Excel ขาดคอลัมน์ที่จำเป็น: {', '.join(missing_cols)}"
                processing_status[job_id]['completed'] = True # ตั้งสถานะเป็นเสร็จสมบูรณ์แต่มี error
            logger.error(f"❌ {processing_status[job_id]['error']}")
            return # หยุดการทำงานของ Thread นี้

        # สร้างโครงสร้างโฟลเดอร์สำหรับเก็บ CSV และ PDF ชั่วคราว
        csv_root_dir = os.path.join(temp_dir, 'CSV')
        pdf_root_dir = os.path.join(temp_dir, 'PDF')
        os.makedirs(csv_root_dir, exist_ok=True) # สร้างถ้ายังไม่มี
        os.makedirs(pdf_root_dir, exist_ok=True)

        # วนลูปประมวลผลแต่ละแถวใน DataFrame (แต่ละ Node/Interface)
        for index, row in df.iterrows():
            with status_lock:
                if processing_status[job_id].get('canceled'): # ตรวจสอบว่างานถูกยกเลิกหรือไม่
                    logger.info(f"⛔ งานถูกยกเลิกโดยผู้ใช้")
                    break # ออกจากลูปถ้าถูกยกเลิก

            node_name = '' # ชื่อ Node สำหรับการ logging และชื่อไฟล์
            csv_success = False # สถานะการสร้าง CSV
            pdf_success = False # สถานะการสร้าง PDF
            error_message = None # ข้อความ error หากมี

            try:
                nod_id = str(row['NodeID']).strip() # Node ID
                itf_id = str(row['Interface ID']).strip() # Interface ID

                # ข้อมูลสำหรับสร้างโครงสร้างโฟลเดอร์
                folder1 = str(row['กระทรวง / สังกัด']).strip()
                folder2 = str(row['กรม / สังกัด']).strip()
                folder3 = str(row['จังหวัด']).strip()
                folder4 = str(row['ชื่อหน่วยงาน']).strip()
                node_name = str(row['Node Name']).strip()

                if not nod_id or not itf_id:
                    error_message = "ข้อมูล NodeID หรือ Interface ID ไม่สมบูรณ์"
                    logger.warning(f"⚠️ ข้ามแถวที่ {index + 1} เนื่องจาก {error_message} (NodeID: '{nod_id}', ITF ID: '{itf_id}')")
                    with status_lock:
                        processing_status[job_id]['processed'] += 1 # เพิ่มจำนวนที่ประมวลผลแล้ว
                        processing_status[job_id]['results'].append({ # บันทึกผลลัพธ์ของแถวนี้
                            'node_name': node_name,
                            'csv_success': False,
                            'pdf_success': False,
                            'error_message': error_message
                        })
                    continue # ข้ามไปยังแถวถัดไป

                logger.info(f"▶ กำลังประมวลผล NodeID: {nod_id}, Interface ID: {itf_id} (แถวที่ {index + 1})")

                # กำหนด Path ของโฟลเดอร์สำหรับ CSV และ PDF ของ Node/Interface ปัจจุบัน
                current_csv_dir = os.path.join(csv_root_dir, folder1, folder2, folder3, folder4)
                current_pdf_dir = os.path.join(pdf_root_dir, folder1, folder2, folder3, folder4)

                os.makedirs(current_csv_dir, exist_ok=True)
                os.makedirs(current_pdf_dir, exist_ok=True)

                raw_json_data = get_data_from_api(nod_id, itf_id, job_id) # ดึงข้อมูลจาก API

                if raw_json_data:
                    # ประมวลผลข้อมูล JSON เพื่อให้พร้อมสำหรับ CSV/PDF
                    headers, processed_daily_data, grand_total_row_data = process_json_data(raw_json_data, job_id, nod_id, folder4)

                    # ทำความสะอาด Node Name เพื่อใช้เป็นชื่อไฟล์ (ลบอักขระที่ไม่ถูกต้องสำหรับชื่อไฟล์)
                    sanitized_node_name = re.sub(r'[\\/:*?"<>|]', '_', node_name)
                    filename_base = f"{sanitized_node_name}"

                    csv_filename = os.path.join(current_csv_dir, f"{filename_base}.csv")
                    pdf_filename = os.path.join(current_pdf_dir, f"{filename_base}.pdf")

                    # สำหรับ CSV: ข้อมูลที่ประมวลผลแล้ว + แถว Grand Total
                    csv_data_to_write = list(processed_daily_data) # สร้างสำเนา
                    if grand_total_row_data:
                        csv_data_to_write.append(grand_total_row_data)

                    # สร้างไฟล์ CSV และ PDF
                    csv_success, csv_msg = export_to_csv(headers, csv_data_to_write, csv_filename, job_id, node_name)
                    pdf_success, pdf_msg = export_to_pdf(headers, processed_daily_data, grand_total_row_data, pdf_filename, job_id, node_name)
                else:
                    error_message = f"ไม่สามารถดึงข้อมูลจาก API ได้สำหรับ NodeID: {nod_id}, Interface ID: {itf_id}"
                    logger.error(f"❌ {error_message}")

            except Exception as e:
                # ดักจับข้อผิดพลาดที่ไม่คาดคิดในการประมวลผลแต่ละแถว
                error_message = f"เกิดข้อผิดพลาดที่ไม่คาดคิดในแถวที่ {index + 1}: {e}"
                logger.error(f"❌ {error_message}")

            finally:
                # อัปเดตสถานะของแถวที่ประมวลผลไปแล้ว
                with status_lock:
                    processing_status[job_id]['processed'] += 1
                    processing_status[job_id]['results'].append({
                        'node_name': node_name,
                        'csv_success': csv_success,
                        'pdf_success': pdf_success,
                        'error_message': error_message
                    })

        # หากงานไม่ถูกยกเลิกหลังจากประมวลผลทุกแถวแล้ว ให้สร้างไฟล์ ZIP
        if not processing_status[job_id].get('canceled'):
            # กำหนดชื่อไฟล์สำหรับดาวน์โหลด
            today_date = datetime.datetime.now().strftime('%Y%m%d')
            download_name = f"{today_date}_SummaryReportbyHour.zip" # แก้ไขการตั้งชื่อไฟล์
            zip_filename_path = os.path.join(temp_dir, download_name)

            if temp_dir and os.path.exists(temp_dir):
                # สร้างไฟล์ ZIP จากเนื้อหาในโฟลเดอร์ชั่วคราว (CSV และ PDF)
                with zipfile.ZipFile(zip_filename_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
                    for root, _, files in os.walk(temp_dir):
                        for file in files:
                            file_path = os.path.join(root, file)
                            # เพิ่มเงื่อนไขเพื่อไม่ให้บีบอัดไฟล์ ZIP ที่กำลังสร้างอยู่
                            if file_path != zip_filename_path: 
                                arcname = os.path.relpath(file_path, temp_dir)
                                zipf.write(file_path, arcname)

                with status_lock:
                    status = processing_status.get(job_id)
                    if status:
                        status['zip_file_path'] = zip_filename_path
                        status['download_name'] = download_name  # อัปเดตชื่อไฟล์สำหรับดาวน์โหลด
                        status['completed'] = True
                    else:
                        logger.error(f"Job {job_id} not found in status list.")
                        return False, "Job not found"

                return True, "รายงานสร้างและบีบอัดสำเร็จแล้ว"

    except Exception as e:
        # ดักจับข้อผิดพลาดระดับสูงที่เกิดขึ้นใน process_file_in_background ทั้งหมด
        with status_lock:
            processing_status[job_id]['error'] = f"เกิดข้อผิดพลาดในระหว่างการประมวลผลเบื้องหลัง: {e}"
            processing_status[job_id]['completed'] = True
        logger.critical(f"❌ {processing_status[job_id]['error']}")

    finally:
        # แก้ไขให้ลบเฉพาะโฟลเดอร์ย่อย
        # เพื่อเก็บไฟล์ ZIP ที่อยู่ในโฟลเดอร์หลักไว้
        if csv_root_dir and os.path.exists(csv_root_dir):
            shutil.rmtree(csv_root_dir, ignore_errors=True)
        if pdf_root_dir and os.path.exists(pdf_root_dir):
            shutil.rmtree(pdf_root_dir, ignore_errors=True)

# --- Flask Routes ---
@app.route('/')
def upload_form():
    """แสดงหน้าฟอร์มสำหรับอัปโหลดไฟล์ Excel (index.html)"""
    return render_template('index.html')

@app.route('/generate_report', methods=['POST'])
def generate_report():
    """
    รับไฟล์ Excel ที่อัปโหลด และเริ่มการประมวลผลในเบื้องหลัง (new thread)
    """
    if 'excel_file' not in request.files:
        return jsonify({"error": "No file part"}), 400 # HTTP 400 Bad Request
    
    file = request.files['excel_file']
    if file.filename == '':
        return jsonify({"error": "No selected file"}), 400
    
    if file:
        job_id = str(uuid.uuid4()) # สร้าง Unique ID สำหรับงานนี้
        file_stream = io.BytesIO(file.read()) # อ่านไฟล์เป็น BytesIO เพื่อส่งให้ Thread อื่น

        # เริ่มต้นสถานะของงานใหม่ (thread-safe)
        with status_lock:
            processing_status[job_id] = {
                'total': -1, # ยังไม่ทราบจำนวนทั้งหมด
                'processed': 0, # จำนวนที่ประมวลผลแล้ว
                'completed': False, # สถานะการเสร็จสมบูรณ์
                'error': None, # ข้อความ error หากมี
                'canceled': False, # สถานะการยกเลิก
                'results': [], # ผลลัพธ์ของแต่ละรายการ
                'temp_dir': None, # โฟลเดอร์ชั่วคราว
                'zip_file_path': None, # Path ของไฟล์ ZIP
                'timestamp': datetime.datetime.now() # เวลาที่เริ่มงาน
            }
        logger.info(f"📂 ได้รับไฟล์ excel '{file.filename}' และเริ่มการประมวลผล")

        # สร้างและเริ่ม Thread สำหรับประมวลผลไฟล์ในเบื้องหลัง
        thread = threading.Thread(target=process_file_in_background, args=(file_stream, job_id))
        thread.daemon = True # ทำให้ Thread สิ้นสุดลงเมื่อโปรแกรมหลักจบ
        thread.start()

        # ส่ง Job ID กลับไปให้ Client เพื่อใช้ติดตามสถานะ
        return jsonify({"message": "Processing started", "job_id": job_id})

@app.route('/status/<job_id>')
def get_status(job_id):
    """
    ตรวจสอบสถานะของงานที่กำลังประมวลผลอยู่
    Client จะเรียก API นี้เป็นระยะๆ เพื่ออัปเดต UI
    """
    with status_lock:
        status = processing_status.get(job_id, {}) # ดึงสถานะงาน (thread-safe)
    return jsonify(status)

@app.route('/logs/<job_id>')
def get_logs(job_id):
    """
    ดึง log ของงานที่กำลังประมวลผลอยู่จาก Queue
    Client จะเรียก API นี้เพื่อแสดง log แบบ Real-time
    """
    logs = []
    # ดึง log จาก queue จนกว่าจะว่าง
    while not log_queue.empty():
        try:
            logs.append(log_queue.get_nowait()) # get_nowait() จะไม่รอถ้า queue ว่าง
        except Exception:
            break
    return jsonify({"logs": logs})


@app.route('/cancel/<job_id>', methods=['POST'])
def cancel_job(job_id):
    """
    รับคำสั่งยกเลิกงานที่กำลังประมวลผลอยู่
    """
    with status_lock:
        if job_id in processing_status:
            processing_status[job_id]['canceled'] = True # ตั้งค่า flag 'canceled' เป็น True
            logger.info(f"⛔ ได้รับคำขอยกเลิกงาน")
            return jsonify({"message": "Job cancellation requested"}), 200
        else:
            logger.warning(f"⚠️ พยายามยกเลิกงานที่ไม่พบ")
            return jsonify({"error": "Job not found"}), 404

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/download_converted_excel/<job_id>')
def download_converted_excel(job_id):
    """
    จัดการการดาวน์โหลดไฟล์ Excel (CSV) ที่ถูกแปลงแล้ว
    """
    with status_lock:
        status = processing_status.get(job_id)
        if not status:
            return jsonify({'error': 'Job ID not found'}), 404

        csv_file_path = status['csv_file_path']
        if not csv_file_path or not os.path.exists(csv_file_path):
            return jsonify({'error': 'File not found'}), 404

    try:
        # ดึงชื่อไฟล์จาก path เพื่อใช้เป็นชื่อไฟล์สำหรับดาวน์โหลด
        filename = os.path.basename(csv_file_path)
        return send_file(csv_file_path, as_attachment=True, download_name=filename)
    except Exception as e:
        logger.error(f"Error downloading file for job {job_id}: {e}")
        return jsonify({'error': 'An error occurred during file download'}), 500

@app.route('/download_report/<job_id>')
def download_report(job_id):
    """
    ให้ผู้ใช้ดาวน์โหลดไฟล์ ZIP ที่สร้างขึ้นเมื่อการประมวลผลเสร็จสมบูรณ์
    """
    with status_lock:
        status_entry = processing_status.get(job_id)

    if status_entry and status_entry['completed'] and status_entry['zip_file_path']:
        # แยกพาธของโฟลเดอร์และชื่อไฟล์ออกจากกัน
        temp_dir = os.path.dirname(status_entry['zip_file_path'])
        zip_filename = os.path.basename(status_entry['zip_file_path'])
        download_name_final = status_entry['download_name']

        # ใช้ send_from_directory อย่างถูกต้อง
        return send_from_directory(
            directory=temp_dir,         # ส่งพาธของโฟลเดอร์ชั่วคราว
            path=zip_filename,          # ส่งแค่ชื่อไฟล์
            as_attachment=True,
            download_name=download_name_final # ใช้ชื่อไฟล์ที่จัดรูปแบบแล้วสำหรับการดาวน์โหลด
        )
    else:
        logger.error(f"❌ ไม่พบไฟล์ ZIP หรือยังสร้างไม่เสร็จ. Path: {status_entry.get('zip_file_path')}")
        return jsonify({"error": "File not found or report not completed."}), 404

def cleanup_old_jobs():
    """
    ฟังก์ชันสำหรับลบสถานะงานและไฟล์ ZIP เก่าๆ ออกจากระบบ
    รันเป็น background process โดยใช้ threading.Timer
    """
    #logger.info("🧹 เริ่มต้นกระบวนการล้างข้อมูลงานเก่า...")
    current_time = datetime.datetime.now()
    jobs_to_remove = [] # list สำหรับเก็บ job_id ของงานที่จะลบ

    retention_hours = 24 # ระยะเวลาเก็บงาน (ในที่นี้คือ 24 ชั่วโมง)
    retention_seconds = retention_hours * 3600

    with status_lock:
        # วนลูปผ่านงานทั้งหมดใน processing_status
        for job_id, job_info in list(processing_status.items()): # ใช้ list(items()) เพื่อให้สามารถลบ item ขณะวนลูปได้
            if job_info.get('completed') and job_info.get('timestamp'):
                job_timestamp = job_info['timestamp']
                # ถ้างานเสร็จสมบูรณ์และเกินระยะเวลาที่กำหนด ให้เพิ่มใน jobs_to_remove
                if (current_time - job_timestamp).total_seconds() > retention_seconds:
                    jobs_to_remove.append(job_id)
            # ถ้างานไม่เสร็จสมบูรณ์ และค้างอยู่นานเกิน 1/4 ของระยะเวลา retention ให้ถือว่าค้างและลบออก
            elif (not job_info.get('completed')) and (current_time - job_info.get('timestamp', current_time)).total_seconds() > (retention_seconds / 4):
                logger.warning(f"⚠️ พบงานค้างเก่า (ไม่สมบูรณ์)")
                jobs_to_remove.append(job_id)


    for job_id in jobs_to_remove:
        with status_lock:
            job_info = processing_status.pop(job_id, None) # ลบงานออกจาก processing_status
        if job_info:
            zip_file_path = job_info.get('zip_file_path')
            # ถ้ามี path ของไฟล์ ZIP และไฟล์มีอยู่จริง ให้ลบไฟล์นั้นด้วย
            if zip_file_path and os.path.exists(zip_file_path):
                try:
                    os.remove(zip_file_path)
                    #logger.info(f"🗑️ ลบไฟล์ ZIP เก่า: {os.path.basename(zip_file_path)} (Job ID: {job_id})")
                except Exception as e:
                    logger.error(f"❌ ข้อผิดพลาดในการลบไฟล์ ZIP เก่า: {e} ")
            logger.info(f"✨ ล้างสถานะงานสำหรับ Job ID: {job_id} แล้ว")
    #logger.info("🧹 กระบวนการล้างข้อมูลงานเก่าเสร็จสมบูรณ์")
    # ตั้งเวลาให้ฟังก์ชันนี้ทำงานอีกครั้งในอนาคต (ทุกครึ่งหนึ่งของระยะเวลา retention)
    threading.Timer(retention_seconds / 2, cleanup_old_jobs).start()

# --- Main Execution Block ---
if __name__ == '__main__':
    # สร้าง Thread สำหรับ cleanup_old_jobs และทำให้เป็น daemon เพื่อให้ Thread จบเมื่อ Main Thread จบ
    cleanup_thread = threading.Thread(target=cleanup_old_jobs)
    cleanup_thread.daemon = True
    cleanup_thread.start()

    # รัน Flask application
    # debug=True จะทำให้ Server รีโหลดอัตโนมัติเมื่อโค้ดเปลี่ยน และแสดง traceback ที่ละเอียดขึ้น
    app.run(debug=True,host= '0.0.0.0',port=5050)

