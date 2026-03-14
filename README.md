# pmed format (p tự đọc từ file)
python3 incremental_sat.py --input pmed1.txt --format pmed

# TSPLIB format (cần chỉ định p)
python3 incremental_sat.py --input TSPLIB/u1060.tsp --format tsplib --p 10

# Chọn solver khác
python3 incremental_sat.py --input pmed1.txt -s glucose4
