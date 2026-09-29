-- Prove2me | Theorems.Thm_Freiman_upper_small_margin
-- name    : Freiman.upper_small_margin
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:10.995556+00:00
-- url     : https://prove2.me/theorems/cd7ce6cc-c3a5-47e6-a80c-0a697eedcc4b
-- title:
--   The small central sum strictly exceeds its noncentral bound
-- statement:
--   Two tails in [Theta2,Theta1] produce a central sum at least h, strictly above B.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:small-family and m2a:peak-margin.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_small_margin (x y : ℝ) (hx : x ∈ Set.Icc upperTheta2 upperTheta1) (hy : y ∈ Set.Icc upperTheta2 upperTheta1) :
    upperSmallBound < 4 + x + y := by
  sorry

end Freiman
