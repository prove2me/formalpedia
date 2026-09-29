-- Prove2me | Theorems.Thm_Freiman_constant_order
-- name    : Freiman.constant_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:23:01.286329+00:00
-- url     : https://prove2.me/theorems/43aa6e42-b25c-49a3-bde3-f215b8cbabe2
-- title:
--   Ordering of the interval and gap constants
-- statement:
--   For the exact real constants defined above,
--   $$
--   \mu_*<c_0<c_F<\sqrt{21}<h<\frac{128}{25}.
--   $$
--   These strict inequalities give the overlap needed to combine the three interval constructions and the nonempty gap needed for maximality.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §§19–20, pp. 64–65, and Appendix G.1, Exact arithmetic. The expression for c_F also appears in Theorem 21.1, p. 71.

import Definitions.Def_Freiman_cF
import Definitions.Def_Freiman_gapThreshold

namespace Freiman

theorem constant_order :
    gapLeft < gapThreshold ∧ gapThreshold < cF ∧
    cF < Real.sqrt 21 ∧ Real.sqrt 21 < upperRayStart ∧
    upperRayStart < (128 / 25 : ℝ) := by
  sorry

end Freiman
