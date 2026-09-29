-- Prove2me | Theorems.Thm_Freiman_upper_small_constants
-- name    : Freiman.upper_small_constants
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:06.025313+00:00
-- url     : https://prove2.me/theorems/4c3c6beb-e142-4bf3-a495-276ec8c383c4
-- title:
--   Exact margins for the small central family and the padding background
-- statement:
--   The report’s constant B lies strictly between 5 and h. The all-3 padding height sqrt(13) also lies strictly below h. These are exact comparisons of the displayed radical expressions.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:peak-margin and the all-3 comparison in the padded-copy argument.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_small_constants  :
    5 < upperSmallBound ∧ upperSmallBound < upperRayStart ∧ Real.sqrt 13 < upperRayStart := by
  sorry

end Freiman
