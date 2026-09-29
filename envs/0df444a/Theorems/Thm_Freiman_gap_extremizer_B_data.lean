-- Prove2me | Theorems.Thm_Freiman_gap_extremizer_B_data
-- name    : Freiman.gap_extremizer_B_data
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:59.328679+00:00
-- url     : https://prove2.me/theorems/1dd81984-1883-4b51-a787-468275a8a9c1
-- title:
--   gap extremizer B data
-- statement:
--   The explicit B word uses only digits 1–4 and contains the exact marked source seed.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; explicit attaining sequence

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_extremizer_B_data : gapDigits gapExtremizerB ∧ gapMatch gapExtremizerB 0 gapSeedB := by
  sorry

end Freiman
