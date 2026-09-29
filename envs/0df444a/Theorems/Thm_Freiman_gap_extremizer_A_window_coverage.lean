-- Prove2me | Theorems.Thm_Freiman_gap_extremizer_A_window_coverage
-- name    : Freiman.gap_extremizer_A_window_coverage
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:15:02.337376+00:00
-- url     : https://prove2.me/theorems/07eb5ab1-c6fb-48e3-89ca-31feee533de5
-- title:
--   gap extremizer A window coverage
-- statement:
--   Every noncentral radius-5 window of the A word is represented by its finite transition range or one of the six phases on either periodic end.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; attainment windows

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_extremizer_A_window_coverage (i : ℤ) (hi : i ≠ 0) : ∃ j ∈ gapARepresentatives, gapLocalWindow gapExtremizerA i 5 = gapLocalWindow gapExtremizerA j 5 := by
  sorry

end Freiman
