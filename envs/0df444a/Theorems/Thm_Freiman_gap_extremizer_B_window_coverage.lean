-- Prove2me | Theorems.Thm_Freiman_gap_extremizer_B_window_coverage
-- name    : Freiman.gap_extremizer_B_window_coverage
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:15:11.106859+00:00
-- url     : https://prove2.me/theorems/38fb546a-eb18-4cb3-8cc6-d2ae1a3127a0
-- title:
--   gap extremizer B window coverage
-- statement:
--   Every noncentral radius-4 window of the B word is represented by its finite transition range or one of the six phases on either periodic end.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; attainment windows

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_extremizer_B_window_coverage (i : ℤ) (hi : i ≠ 0) : ∃ j ∈ gapBRepresentatives, gapLocalWindow gapExtremizerB i 4 = gapLocalWindow gapExtremizerB j 4 := by
  sorry

end Freiman
