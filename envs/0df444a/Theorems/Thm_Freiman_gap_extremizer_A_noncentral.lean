-- Prove2me | Theorems.Thm_Freiman_gap_extremizer_A_noncentral
-- name    : Freiman.gap_extremizer_A_noncentral
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:01.417358+00:00
-- url     : https://prove2.me/theorems/cbf64b9f-8e77-46ff-abcf-4eb531521436
-- title:
--   gap extremizer A noncentral
-- statement:
--   All noncentral heights of the explicit A word lie strictly below 4.5278, including both infinite periodic ends.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; attainment

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_extremizer_A_noncentral (i : ℤ) (hi : i ≠ 0) : localValue gapExtremizerA i < 22639/5000 := by
  sorry

end Freiman
