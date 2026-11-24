-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_price_under_integral
-- name    : GrothendieckLB.Supplement.cq_gaussian_price_under_integral
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T21:52:48.349773+00:00
-- url     : https://prove2.me/theorems/e0a7002c-e57e-4a82-ba6f-5864d993ab81
-- title:
--   Complex Price formula under the spatial Gaussian integral
-- statement:
--   Consider a test function with a complex parameter and two real spatial variables, integrated against the Gaussian of spatial covariance equal to the negative parameter. Its complex derivative is the Gaussian integral of the parameter derivative minus the Gaussian integral of the mixed spatial derivative. Measurability and uniform polynomial growth of the four functions on each compact subdisk suffice for the conclusion.
-- source:
--   Independent Price differentiation and rational interval certificate for Saha et al., arXiv:2608.11158v2. The density identity is Prove2Me bb4bfdfc-4dcc-425d-8a98-1b646de8d12b.

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace GrothendieckLB.Supplement
open CQPrice MeasureTheory

theorem cq_gaussian_price_under_integral (f g fx fxy : ℂ → ℝ×ℝ → ℂ) (z : ℂ) (hz : ‖z‖<1)
    (hm : ∀ H∈[f,g,fx,fxy], ∀ t : ℂ, ‖t‖<1 → Measurable (H t))
    (hp : ∀ H∈[f,g,fx,fxy], ∀ R : ℝ, 0≤R → R<1 → ∃ C : ℝ, 0≤C ∧ ∃ k : ℕ,
      ∀ t : ℂ, ‖t‖≤R → ∀ w : ℝ×ℝ, ‖H t w‖≤ C*((1+|w.1|)*(1+|w.2|))^k)
    (hd : ∀ t : ℂ, ‖t‖<1 → ∀ w : ℝ×ℝ, HasDerivAt (fun s : ℂ => f s w) (g t w) t)
    (hx : ∀ x y : ℝ, HasDerivAt (fun X : ℝ => f z (X,y)) (fx z (x,y)) x)
    (hy : ∀ x y : ℝ, HasDerivAt (fun Y : ℝ => fx z (x,Y)) (fxy z (x,y)) y) :
    HasDerivAt (fun t : ℂ => ∫ w : ℝ×ℝ, density (-t) w.1 w.2*f t w)
      ((∫ w : ℝ×ℝ, density (-z) w.1 w.2*g z w)-
        ∫ w : ℝ×ℝ, density (-z) w.1 w.2*fxy z w) z := by sorry

end GrothendieckLB.Supplement
