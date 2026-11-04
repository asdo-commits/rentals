#!/usr/bin/env python3
"""Collects Vancouver rental listings from Craigslist and JPCanada into data.json.

Runs on GitHub Actions every 2 hours. Keeps listings it has seen before for a while
(live=false once they drop out of the search) so saved listings do not vanish.
"""
import html as htmllib
import io
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from urllib.parse import urljoin
from zoneinfo import ZoneInfo

ROOT = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(ROOT, "data.json")
PHOTO_DIR = os.path.join(ROOT, "photos")
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
PT = ZoneInfo("America/Vancouver")
MAX_PRICE = 1200
MIN_PRICE = 250
KEEP_DAYS = 45
REV = 3
MAX_NEW_PER_SOURCE = 40
MAX_PHOTOS = 6
DOWNTOWN = (49.2827, -123.1207)

NOW = datetime.now(PT)
START = time.time()
BUDGET = 420  # seconds; after this no new listings are fetched, the next scan continues


def out_of_time():
    return time.time() - START > BUDGET

TODAY = NOW.date()


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def get(url, binary=False, tries=2):
    log("GET", url[:110])
    last = None
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept-Language": "en"})
            with urllib.request.urlopen(req, timeout=20) as r:
                body = r.read()
            return body if binary else body.decode("utf-8", "replace")
        except Exception as e:  # noqa: BLE001
            last = e
            time.sleep(1.5)
    raise last


# ---------------------------------------------------------------- shared helpers

def km(lat1, lon1, lat2, lon2):
    from math import radians, sin, cos, asin, sqrt
    dlat, dlon = radians(lat2 - lat1), radians(lon2 - lon1)
    a = sin(dlat / 2) ** 2 + cos(radians(lat1)) * cos(radians(lat2)) * sin(dlon / 2) ** 2
    return 6371 * 2 * asin(sqrt(a))


def in_zone1(lat, lon):
    """City of Vancouver plus UBC, roughly. Excludes Burnaby, Richmond and the North Shore."""
    if not (49.195 <= lat <= 49.300 and -123.272 <= lon <= -123.023):
        return False
    if lon < -123.225 and not (49.235 <= lat <= 49.285):
        return False
    if lat < 49.205 and lon > -123.14:  # Fraser river edge, Richmond tip
        return lon < -123.03 and lat > 49.2
    return True


def area_of(lat, lon):
    d = km(lat, lon, *DOWNTOWN)
    if d <= 2.2 and lat >= 49.268:
        return "dt"
    if d <= 5.5:
        return "near"
    return "other"


def tier_ok(price):
    return MIN_PRICE <= price <= MAX_PRICE


def iso_local(ts):
    return datetime.fromtimestamp(ts, PT).strftime("%Y-%m-%dT%H:%M")


MON = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
MONFULL = ["January", "February", "March", "April", "May", "June", "July", "August",
           "September", "October", "November", "December"]


def avail_from_date(d):
    days = (d - TODAY).days
    if days <= 0:
        return "Available now", True, 0
    return "Available %s %d" % (MON[d.month - 1], d.day), True, days


def avail_from_text(text):
    t = text.lower()
    if re.search(r"available (now|immediately)|immediate(ly)? (move|occupancy|available)|move[- ]in (now|immediately)|"
                 r"ready (now|to move)|即日|すぐに?入居|即入居", t):
        return "Available now", True, 0
    m = re.search(r"(?:available|avail\.?|move[- ]in|from|starting|start)\s*(?:on|from|:)?\s*"
                  r"(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\.?\s*(\d{1,2})", t)
    if m:
        mo = MON.index(m.group(1).capitalize()) + 1
        day = int(m.group(2))
        yr = TODAY.year + (1 if mo < TODAY.month - 1 else 0)
        try:
            return avail_from_date(datetime(yr, mo, day).date())
        except ValueError:
            pass
    m = re.search(r"(\d{1,2})月(\d{1,2})日?(?:から|より|入居|こら)", text)
    if m:
        mo, day = int(m.group(1)), int(m.group(2))
        yr = TODAY.year + (1 if mo < TODAY.month - 1 else 0)
        try:
            return avail_from_date(datetime(yr, mo, day).date())
        except ValueError:
            pass
    m = re.search(r"(?:available|move[- ]in)\s*(?:in|from|on)?\s*(?:early |mid |late |end of )?"
                  r"(january|february|march|april|may|june|july|august|september|october|november|december)", t)
    if m:
        name = m.group(1).capitalize()
        return "Available in " + name, True, 5
    m = re.search(r"(\d{1,2})月(?:中)?(?:から|より|入居|頭)", text)
    if m:
        mo = int(m.group(1))
        if 1 <= mo <= 12:
            return "Available in " + MONFULL[mo - 1], True, 5
    return "Availability not stated, ask poster", False, 9


def stay_from_text(text):
    t = text.lower()
    note = ""
    months = None
    m = re.search(r"(?:minimum|min\.?|at least|min stay|lease(?: term)?)\D{0,12}(\d{1,2})\s*(?:-|to)?\s*(?:\d{1,2})?\s*(?:months?|mos?\b)", t)
    if m:
        months = int(m.group(1))
        note = "Minimum %d months" % months
    if months is None:
        m = re.search(r"(\d{1,2})\s*[- ]?(?:months?|mos?\b)\s*(?:minimum|min|lease|term|or more|\+)", t)
        if m:
            months = int(m.group(1))
            note = "Minimum %d months" % months
    if months is None:
        m = re.search(r"最短(\d{1,2})\s*(?:ヶ|ケ|か|ヵ)?月", text) or \
            re.search(r"(\d{1,2})\s*(?:ヶ|ケ|か|ヵ)?月(?:以上|から|　以上)", text)
        if m:
            months = int(m.group(1))
            note = "Minimum %d months" % months
    if months is None and re.search(r"1[- ]?year|one[- ]year|12[- ]month|annual lease|1年", t):
        months = 12
        note = "1 year"
    if months is None and re.search(r"month[- ]to[- ]month|short[- ]term|short term|sublet|sublease|短期", t):
        return "short", "Short term or month to month"
    if months is None:
        return "unk", ""
    if months >= 12:
        return "long", note
    if months >= 6:
        return "mid", note
    return "short", note


SHARED_BATH = re.compile(
    r"shar(?:e|ed|ing)\s+(?:the\s+|a\s+)?(?:bath|washroom|restroom|shower|toilet)|"
    r"(?:bath(?:room)?|washroom)\s+(?:is\s+)?shar(?:e|ed)|shared\s+(?:full\s+)?(?:bath|washroom)|"
    r"(?:共用|共有|シェア)\s*(?:の)?(?:バス|トイレ|シャワー|浴室)|"
    r"(?:バス|トイレ|シャワー)[^。\n]{0,6}(?:共用|共有|シェア)", re.I)
PRIVATE_BATH = re.compile(
    r"private\s+(?:bath|washroom|bathroom|shower|ensuite|suite)|own\s+(?:private\s+)?(?:bath|washroom|bathroom)|en-?suite|"
    r"attached\s+(?:bath|washroom)|bath(?:room)?\s+attached|(?:bath|washroom)\s+(?:is\s+)?private|"
    r"専用\s*(?:の)?(?:バス|シャワー|トイレ|浴室|ユニット|ブース)|"
    r"(?:バス|シャワー|トイレ)[^。\n]{0,4}専用|"
    r"バス(?:ルーム)?(?:・トイレ)?付|プライベート\s*(?:バス|ユニット)|"
    r"シャワー[、,・ ]*トイレ[^。\n]{0,12}(?:付|専用|部屋)|ユニットバス付", re.I)
MALE_ONLY = re.compile(r"(?<!fe)male[s]?\s+(?:only|preferred|student)|men\s+only|boys?\s+only|gentlem[ae]n|"
                       r"男性限定|男性のみ|男性専用", re.I)
FEMALE_ONLY = re.compile(r"female|women|woman|ladies|girls?\b|女性", re.I)


def bath_state(text):
    """Returns (ok, label). ok False means the bathroom is shared."""
    priv = bool(PRIVATE_BATH.search(text))
    shared = bool(SHARED_BATH.search(text))
    if priv:
        return True, "Private bathroom" + (" (poster also mentions a shared one, check)" if shared else "")
    if shared:
        return False, "Shared"
    return None, ""


def clean_text(s):
    s = re.sub(r"<br\s*/?>", "\n", s or "", flags=re.I)
    s = re.sub(r"<[^>]+>", " ", s)
    return re.sub(r"[ \t]+", " ", htmllib.unescape(s)).strip()


def first_sentences(text, n=2, limit=200):
    flat = re.sub(r"\s+", " ", text).strip()
    parts = re.split(r"(?<=[.!?。])\s+", flat)
    out = " ".join(parts[:n])
    return out[:limit].rstrip()


def note_from(text, roommates=False):
    t = re.sub(r"\s+", " ", text)
    bits = ["Lives with roommates."] if roommates else []
    for pat, label in [
        (r"(utilities|wifi|wi-fi|internet|hydro)[^.]{0,40}(included|incl)", "Utilities or internet included."),
        (r"no (pets?|smoking|smokers)", "No pets or smoking."),
        (r"female only|women only|女性限定|女性のみ", "Women only."),
        (r"furnished", "Furnished."),
        (r"家具付", "Furnished."),
        (r"laundry", "Laundry available."),
    ]:
        if re.search(pat, t, re.I) and label not in bits:
            bits.append(label)
    return " ".join(bits[:4])


APT_WORDS = re.compile(r"studio|\bsuite\b|1[- ]?bed(?:room)?\b|one[- ]bed|\bcondo\b|apartment|basement|\bloft\b|"
                       r"スタジオ|アパート|コンドミニアム|"
                       r"ワンベッド|1ベッド|ベースメント", re.I)
ROOM_WORDS = re.compile(r"\broom\b|roommate|room ?mate|shared house|sharehouse|homestay|個室|ルームメイト|"
                        r"シェアハウス|ホームステイ|お部屋|部屋", re.I)


WHOLE = re.compile(r"studio|\bsuite\b|\b1[- ]?bed(?:room)?s?\b|one[- ]bed|\b[1-3][- ]?br\b|\bbachelor\b|micro|laneway|\bcondo\b|"
                   r"apartment|\bloft\b|basement|house for rent|\bunit\b|\u30b9\u30bf\u30b8\u30aa|\u30a2\u30d1\u30fc\u30c8|"
                   r"\u30b3\u30f3\u30c9\u30df\u30cb\u30a2\u30e0|\u30ef\u30f3\u30d9\u30c3\u30c9|1\u30d9\u30c3\u30c9|\u30d9\u30fc\u30b9\u30e1\u30f3\u30c8", re.I)
SHAREY = re.compile(r"\bshar(?:e|ed|ing)\b|roommates?|room ?mates?|looking for \d|per (?:person|room)|\brooms? (?:for rent|available|share)|"
                    r"\bprivate r(?:oo)?m\b|bedroom (?:available|for rent)|single room|master (?:bed)?room|homestay|\bone bed ?room for rent|"
                    r"\u30b7\u30a7\u30a2|\u500b\u5ba4|\u30eb\u30fc\u30e0\u30e1\u30a4\u30c8|\u30db\u30fc\u30e0\u30b9\u30c6\u30a4", re.I)


def kind_of(title, body, category, bedrooms=None):
    t = title or ""
    if category == "roo":
        return "room"
    if SHAREY.search(t):
        return "room"
    if WHOLE.search(t):
        return "apt"
    if re.search(r"\b(room|rm|bedroom)\b|\u304a\u90e8\u5c4b|\u90e8\u5c4b", t, re.I):
        return "room"
    return "room"


def whole_unit_sure(title, body):
    """True only when the post clearly offers a whole place, not a room in a shared home."""
    return bool(WHOLE.search(title)) and not SHAREY.search(title) and not SHAREY.search(body[:400])


# ------------------------------------------------------------------ Craigslist

SAPI = ("https://sapi.craigslist.org/web/v8/postings/search/full?batch=16-0-360-0-0&cc=US&lang=en"
        "&max_price=%d&sort=date&searchPath=%s%s")


def cl_search(path):
    extra = "&private_bath=1" if path in ("roo", "sub") else ""
    raw = get(SAPI % (MAX_PRICE, path, extra))
    d = json.loads(raw)["data"]
    dc = d["decode"]
    out = []
    for it in d["items"]:
        try:
            pid = dc["minPostingId"] + it[0]
            posted = dc["minPostedDate"] + it[1]
            price = it[3]
            loc = it[4].split("~")
            lat, lon = float(loc[1]), float(loc[2])
            uuid = next((x[1] for x in it if isinstance(x, list) and x and x[0] == 13), None)
            title = next((x for x in it if isinstance(x, str) and " " in x and not x.startswith(("1:", "2:", "3:", "4:", "5:"))), "")
            imgs = next(([i.split(":", 1)[1] for i in x[1:]] for x in it if isinstance(x, list) and x and x[0] == 4), [])
            out.append(dict(pid=pid, posted=posted, price=price, lat=lat, lon=lon, uuid=uuid, title=title,
                            imgs=imgs, path=path))
        except Exception:  # noqa: BLE001
            continue
    return out


def cl_candidates():
    seen, out = set(), []
    for path in ("apa", "roo", "sub"):
        try:
            rows = cl_search(path)
        except Exception as e:  # noqa: BLE001
            log("craigslist search failed", path, e)
            continue
        for r in rows:
            if r["pid"] in seen:
                continue
            seen.add(r["pid"])
            if not r["uuid"] or not tier_ok(r["price"]):
                continue
            if (NOW.timestamp() - r["posted"]) > 21 * 86400:
                continue
            if not in_zone1(r["lat"], r["lon"]):
                continue
            out.append(r)
        log("craigslist", path, len(rows), "rows, kept so far", len(out))
    return out


def cl_listing(r):
    raw = get("https://sapi.craigslist.org/web/v8/postings/%s?lang=en&cc=US" % r["uuid"])
    item = json.loads(raw)["data"]["items"][0]
    body = clean_text(item.get("body", ""))
    title = item.get("title") or r["title"]
    text = title + "\n" + body
    attrs = {a.get("postingAttributeKey"): a.get("value") for a in item.get("attributes", [])}
    if MALE_ONLY.search(text) and not FEMALE_ONLY.search(text):
        return None, "male only"
    ok, bath = bath_state(text)
    bath_unclear = False
    kind = kind_of(title, body, r["path"], attrs.get("bedrooms"))
    if ok is False:
        return None, "shared bath"
    if ok is None:
        if kind == "apt" and r["path"] != "roo" and whole_unit_sure(title, body):
            bath = "Private (whole unit)"
        elif r["path"] in ("roo", "sub"):
            bath = "Private bathroom (listed as private)"
        else:
            bath = "Not stated, ask poster"
            bath_unclear = True
    loc = item.get("location", {})
    lat, lon = loc.get("lat", r["lat"]), loc.get("lon", r["lon"])
    if not in_zone1(lat, lon):
        return None, "outside zone 1"
    if attrs.get("movein_date"):
        try:
            avail, known, asort = avail_from_date(datetime.strptime(attrs["movein_date"], "%Y-%m-%d").date())
        except ValueError:
            avail, known, asort = avail_from_text(text)
    else:
        avail, known, asort = avail_from_text(text)
    stay, stay_note = stay_from_text(text)
    addr = loc.get("displayAddress") or loc.get("neighborhood") or loc.get("description") or "Address not given"
    if loc.get("description") and loc.get("description").lower() not in addr.lower():
        addr = "%s, %s" % (addr, loc["description"])
    imgs = item.get("images") or r["imgs"]
    imgs = [i.split(":", 1)[1] if ":" in i else i for i in imgs][:MAX_PHOTOS]
    url = item.get("url") or "https://www.craigslist.org/view/d/%s" % r["uuid"]
    rec = dict(
        id="cl%d" % r["pid"], listed=iso_local(item.get("postedDate", r["posted"])), kind=kind,
        area=area_of(lat, lon), price=int(item.get("price") or r["price"]), title=title[:120], addr=addr[:120],
        bath=bath, avail=avail, availKnown=known, availSort=asort, stay=stay,
        stayNote=stay_note or "Not stated", src="Craigslist", url=url, posted="",
        note=note_from(body, roommates=(kind == "room" or bool(SHAREY.search(title)))), lat=lat, lng=lon, r=500,
        photo_src=["https://images.craigslist.org/%s_600x450.jpg" % i for i in imgs],
    )
    if bath_unclear:
        rec["unclear"] = True
    return rec, None


# -------------------------------------------------------------------- JPCanada

JP_BASE = "https://bbs.jpcanada.com/"
NEG_PLACE = re.compile(r"burnaby|richmond|surrey|coquitlam|north\s*van|west\s*van|langley|delta|new\s*west|port\s*moody|"
                       r"metrotown|brentwood|lougheed|lonsdale|maple ridge|abbotsford|"
                       r"バーナビー|リッチモンド|サレー|コキットラム|"
                       r"ノースバン|ウエストバン|ラングリー|デルタ|ニューウエスト|"
                       r"メトロタウン|ブレントウッド|ノス", re.I)
POS_PLACE = re.compile(r"vancouver|downtown|zone\s*1|1\s*zone|ubc|kitsilano|\bkits\b|joyce|collingwood|marpole|mount pleasant|fairview|"
                       r"yaletown|west end|gastown|chinatown|strathcona|main st|commercial|oakridge|dunbar|kerrisdale|point grey|"
                       r"renfrew|hastings|cambie|granville|broadway|coal harbour|olympic village|fraserview|killarney|victoria dr|"
                       r"langara|south van|east van|バンクーバー|ダウンタウン|ゾーン\s*1|ゾーン1|"
                       r"キツラノ|ジョイス|メイン|カンビー|イーストバン|"
                       r"ヤレタウン|ウエストエンド|ゲイスタウン", re.I)

# Rough centre points for placing the approximate map circle.
JP_PLACES = [
    (r"gastown|ガスタウン", (49.2840, -123.1085)),
    (r"yaletown|ヤレタウン", (49.2745, -123.1220)),
    (r"west end|ウエストエンド", (49.2850, -123.1330)),
    (r"coal harbour", (49.2900, -123.1250)),
    (r"chinatown|strathcona", (49.2795, -123.0990)),
    (r"kitsilano|\bkits\b|キツラノ", (49.2680, -123.1550)),
    (r"fairview|broadway|ブロードウェイ", (49.2640, -123.1260)),
    (r"mount pleasant|main st|メイン", (49.2630, -123.1010)),
    (r"commercial", (49.2700, -123.0690)),
    (r"joyce|collingwood|ジョイス", (49.2382, -123.0316)),
    (r"renfrew", (49.2580, -123.0450)),
    (r"hastings", (49.2810, -123.0450)),
    (r"oakridge|cambie|langara", (49.2260, -123.1170)),
    (r"marpole", (49.2080, -123.1300)),
    (r"dunbar", (49.2500, -123.1850)),
    (r"kerrisdale", (49.2340, -123.1560)),
    (r"point grey", (49.2650, -123.1900)),
    (r"ubc", (49.2606, -123.2460)),
    (r"killarney|fraserview|victoria dr", (49.2150, -123.0650)),
    (r"east van|イーストバン", (49.2650, -123.0700)),
    (r"downtown|ダウンタウン", (49.2827, -123.1207)),
]


def jp_list():
    h = get(JP_BASE + "listing.php?bbs=3&order=0")
    out = []
    for blk in h.split('<div class="bbs-row">')[1:]:
        m = re.search(r"msgid=(\d+)", blk)
        if not m:
            continue
        mid = m.group(1)
        tm = re.search(r'msgid=\d+[^"]*"[^>]*>([^<]+)</a>', blk)
        title = htmllib.unescape(tm.group(1)).strip() if tm else ""
        pm = re.search(r'priceinfo">\s*\$?\s*([\d,]+)', blk)
        price = int(pm.group(1).replace(",", "")) if pm else None
        dm = re.search(r"(\d{4}-\d{2}-\d{2} \d{2}:\d{2}):\d{2}", blk)
        lm = re.search(r'txt-red">([^<]*)<', blk)
        out.append(dict(mid=mid, title=title, price=price, when=dm.group(1) if dm else None,
                        label=htmllib.unescape(lm.group(1)).strip() if lm else ""))
    return out


def jp_candidates():
    try:
        rows = jp_list()
    except Exception as e:  # noqa: BLE001
        log("jpcanada list failed", e)
        return []
    cutoff = NOW.replace(tzinfo=None) - timedelta(days=14)
    out = []
    for r in rows:
        if r["price"] is None or not tier_ok(r["price"]):
            continue
        try:
            when = datetime.strptime(r["when"], "%Y-%m-%d %H:%M")
        except Exception:  # noqa: BLE001
            continue
        if when < cutoff:
            continue
        if re.search(r"ライド|車を譲|買|販売|求人|対う|チケット", r["title"]):
            continue
        out.append(r)
    log("jpcanada", len(rows), "rows,", len(out), "in range")
    return out


def jp_listing(r):
    h = get(JP_BASE + "topics.php?bbs=3&msgid=%s&order=0&cat=&&dummy=0" % r["mid"])
    # The page also shows neighbouring posts. Keep only this one.
    start = h.find("No.%s" % r["mid"])
    if start < 0:
        start = 0
    nxt = h.find("topicHeaderTable", start + 50)
    seg = h[start: nxt if nxt > 0 else len(h)]
    body_m = re.search(r'topic-content[^>]*>(.*)', seg, re.S)
    body = clean_text(body_m.group(1) if body_m else seg)
    body = re.split(r"この賃貸についてEmail|この話題について", body)[0]
    title = r["title"]
    text = title + "\n" + body + "\n" + r["label"]
    if MALE_ONLY.search(text) and not FEMALE_ONLY.search(text):
        return None, "male only"
    label_place = r["label"].split("/")[-1] if "/" in r["label"] else r["label"]
    pos_title = bool(POS_PLACE.search(title + " " + label_place))
    neg_title = bool(NEG_PLACE.search(title + " " + label_place))
    pos_body = bool(POS_PLACE.search(body))
    unclear = False
    loc_unclear = False
    if neg_title and not pos_title:
        return None, "outside zone 1"
    if not (pos_title or pos_body):
        if NEG_PLACE.search(body):
            return None, "outside zone 1"
        unclear = True
        loc_unclear = True
    ok, bath = bath_state(text)
    if ok is False:
        return None, "shared bath"
    kind = kind_of(title, body, "jp")
    if ok is None:
        if kind == "apt" and whole_unit_sure(title, body):
            bath = "Private (whole unit)"
        else:
            bath = "Not stated, ask poster"
            unclear = True
    # centre point for the approximate circle
    lat, lon = 49.2600, -123.1100
    place_txt = None
    for hay in (title + " " + label_place, body):
        for pat, ll in JP_PLACES:
            mm = re.search(pat, hay, re.I)
            if mm:
                lat, lon = ll
                place_txt = mm.group(0).strip()
                break
        if place_txt:
            break
    avail, known, asort = avail_from_text(text)
    stay, stay_note = stay_from_text(text)
    pm = re.search(r"\$\s?([\d,]{3,5})", body)
    price = r["price"]
    imgs = []
    for m in re.finditer(r'(?:src|href)="([^"]*uploads/3/%s-0-(\d+)-[a-z]\.jpg)"' % r["mid"], h):
        n = int(m.group(2))
        if n not in [i[0] for i in imgs]:
            imgs.append((n, m.group(1)))
    imgs.sort()
    photo_src = [urljoin(JP_BASE, p) for _, p in imgs][:MAX_PHOTOS]
    addr = label_place or "Vancouver"
    if place_txt:
        addr = "Near " + (place_txt.title() if place_txt.isascii() else place_txt)
    if loc_unclear:
        addr = "Location not clear in the post"
    when = datetime.strptime(r["when"], "%Y-%m-%d %H:%M")
    rec = dict(
        id="jp%s" % r["mid"], listed=when.strftime("%Y-%m-%dT%H:%M"), kind=kind,
        area=area_of(lat, lon) if not loc_unclear else "other", price=price, title=title[:120], addr=addr[:120],
        bath=bath, avail=avail, availKnown=known, availSort=asort, stay=stay,
        stayNote=stay_note or "Not stated", src="JPCanada",
        url=JP_BASE + "topics.php?bbs=3&msgid=%s" % r["mid"], posted="",
        note=note_from(body, roommates=(kind == "room")), lat=lat, lng=lon, r=700, photo_src=photo_src,
        ja=dict(title=title[:120]),
    )
    if unclear:
        rec["unclear"] = True
    return rec, None


# ---------------------------------------------------------------------- photos

def save_photos(rec):
    try:
        from PIL import Image
    except ImportError:
        log("Pillow missing, no photos")
        return []
    os.makedirs(PHOTO_DIR, exist_ok=True)
    paths = []
    for n, u in enumerate(rec.get("photo_src", [])[:MAX_PHOTOS]):
        rel = "photos/%s-%d.jpg" % (rec["id"], n)
        full = os.path.join(ROOT, rel)
        if os.path.exists(full):
            paths.append(rel)
            continue
        try:
            im = Image.open(io.BytesIO(get(u, binary=True))).convert("RGB")
            w, h = im.size
            target = 4 / 3
            if w / h > target:
                nw = int(h * target)
                im = im.crop(((w - nw) // 2, 0, (w - nw) // 2 + nw, h))
            else:
                nh = int(w / target)
                im = im.crop((0, 0, w, nh))
            im = im.resize((420, 315))
            im.save(full, "JPEG", quality=68, optimize=True)
            paths.append(rel)
        except Exception as e:  # noqa: BLE001
            log("photo failed", u, e)
    return paths


# ------------------------------------------------------------------------ main

def dupe_key(r):
    return (r.get("src"), re.sub(r"\W+", "", (r.get("title") or "").lower()), r.get("price"),
            round(r.get("lat", 0), 3), round(r.get("lng", 0), 3))


def main():
    prev = {}
    try:
        with open(DATA, encoding="utf-8") as f:
            for l in json.load(f).get("listings", []):
                if l.get("rev") != REV:
                    continue  # made by an older version of the rules, look at it again
                prev[l["id"]] = l
    except Exception:  # noqa: BLE001
        pass

    live_ids = set()
    new_recs = {}
    skipped = {}

    cl = cl_candidates()
    jp = jp_candidates()
    for src_name, cands, fetch, idf in (("craigslist", cl, cl_listing, lambda r: "cl%d" % r["pid"]),
                                         ("jpcanada", jp, jp_listing, lambda r: "jp%s" % r["mid"])):
        fresh = 0
        for r in cands:
            lid = idf(r)
            if lid in prev and not prev[lid].get("skip"):
                live_ids.add(lid)
                continue
            if lid in prev and prev[lid].get("skip"):
                continue
            if fresh >= MAX_NEW_PER_SOURCE or out_of_time():
                log("stopping early:", "time budget" if out_of_time() else "per-source cap")
                break
            fresh += 1
            try:
                rec, why = fetch(r)
            except Exception as e:  # noqa: BLE001
                log("detail failed", lid, e)
                continue
            time.sleep(0.4)
            if rec is None:
                skipped[lid] = dict(id=lid, skip=True, why=why, seen=NOW.strftime("%Y-%m-%d"), rev=REV)
                log("skip", lid, why)
                continue
            key = dupe_key(rec)
            if any(dupe_key(o) == key for o in list(prev.values()) + list(new_recs.values()) if not o.get("skip")):
                skipped[lid] = dict(id=lid, skip=True, why="duplicate", seen=NOW.strftime("%Y-%m-%d"), rev=REV)
                log("skip", lid, "duplicate")
                continue
            rec["rev"] = REV
            rec["photos"] = save_photos(rec)
            rec.pop("photo_src", None)
            new_recs[lid] = rec
            live_ids.add(lid)
            log("new", lid, rec["price"], rec["title"][:50])

    listings = []
    today_s = NOW.strftime("%Y-%m-%d")
    merged = {}
    merged.update(prev)
    merged.update(new_recs)
    merged.update(skipped)
    for lid, rec in merged.items():
        if rec.get("skip"):
            # remember skipped ids for 30 days so they are not refetched every run
            try:
                age = (TODAY - datetime.strptime(rec["seen"], "%Y-%m-%d").date()).days
            except Exception:  # noqa: BLE001
                age = 99
            if age <= 30:
                listings.append(rec)
            continue
        rec["live"] = lid in live_ids
        if rec["live"]:
            rec["lastSeen"] = today_s
        last = rec.get("lastSeen") or today_s
        try:
            age = (TODAY - datetime.strptime(last, "%Y-%m-%d").date()).days
        except Exception:  # noqa: BLE001
            age = 0
        if age > KEEP_DAYS:
            for rel in rec.get("photos", []):
                try:
                    os.remove(os.path.join(ROOT, rel))
                except OSError:
                    pass
            continue
        listings.append(rec)

    shown = [l for l in listings if not l.get("skip")]
    if not shown and not cl and not jp:
        log("nothing came back from either source; keeping the old file untouched")
        sys.exit(0)

    out = dict(asOf=NOW.strftime("%Y-%m-%dT%H:%M"), listings=sorted(listings, key=lambda l: l["id"]))
    with open(DATA, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, separators=(",", ":"))
    log("wrote", len(shown), "listings,", sum(1 for l in shown if l.get("live")), "live,", len(new_recs), "new")


if __name__ == "__main__":
    main()
