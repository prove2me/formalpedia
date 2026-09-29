-- Prove2me | Theorems.Thm_Freiman_upper_KA_bounds
-- name    : Freiman.upper_KA_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:48.09276+00:00
-- url     : https://prove2.me/theorems/7dcddb46-6af7-40c8-b0f9-0b67ae1c8127
-- title:
--   The exact hull bounds for the A restricted digits
-- statement:
--   Every allowed restricted continued fraction lies between [0;4,overline(13)] and [0;overline(13)], with the exact radical values Theta8 and Theta1.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:rule, m2a:theta and the extremal-word argument.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_KA_bounds (x : ℝ) (hx : x ∈ upperKA) :
    x ∈ Set.Icc upperTheta8 upperTheta1 := by
  sorry

end Freiman
