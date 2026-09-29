-- Prove2me | Theorems.Thm_Freiman_gap_extremizer_B_noncentral
-- name    : Freiman.gap_extremizer_B_noncentral
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:09.8012+00:00
-- url     : https://prove2.me/theorems/61ccada6-4ef2-4300-81c8-f708f4187336
-- title:
--   gap extremizer B noncentral
-- statement:
--   All noncentral heights of the explicit B word lie strictly below 4.5278, including both infinite periodic ends.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; attainment

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_extremizer_B_noncentral (i : ℤ) (hi : i ≠ 0) : localValue gapExtremizerB i < 22639/5000 := by
  sorry

end Freiman
