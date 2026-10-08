-- Prove2me | Theorems.Thm_Helfgott_etaStar_expSum_norm_le_of_etaTwo_bound
-- name    : Helfgott.etaStar_expSum_norm_le_of_etaTwo_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T23:08:40.699633+00:00
-- url     : https://prove2.me/theorems/033cbed5-0513-42b3-9261-b610463f8cb6
-- title:
--   Transfer of a large-scale compact minor-arc bound with explicit Gaussian tail error
-- statement:
--   Let x>0, a>0, B≥0 and fix a frequency α. If |Sη₂(xw/49,α)|≤B(xw/49) for every w≥a, then the actual Gaussian-convolved sum satisfies |Sη*(x,α)|≤(x/49)(B√(π/2)+5a³). The assumption is precisely the remaining compact-smoothing estimate over its valid scales. The small-scale range 0<w<a is bounded here without assumptions by a proved Chebyshev estimate |Sη₂(y,α)|≤15y and the Gaussian mass estimate ∫₀ᵃφ(w)dw≤a³/3. This is a conditional analytic transfer theorem, not an unconditional minor-arc or Goldbach proof.
-- source:
--   Derived quantitative transfer from Helfgott, arXiv:1312.7748v2, equation (4.9) and the scale-domain issue in Proposition 4.5. https://arxiv.org/html/1312.7748v2 . The error 5a³ is derived here from Mathlib’s Chebyshev bound and φ(w)≤w²; it is not a quoted constant from the paper. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
open MeasureTheory

namespace Helfgott

theorem etaStar_expSum_norm_le_of_etaTwo_bound (x a B : ℝ) (hx : 0 < x) (ha : 0 < a) (hB : 0 ≤ B)
    (α : AddCircle (1 : ℝ))
    (hcompact : ∀ w : ℝ, a ≤ w →
      ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
        etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ ≤ B*(x*w/49)) :
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α‖ ≤
      (x/49)*(B*Real.sqrt (Real.pi/2)+5*a^3) := by sorry

end Helfgott
