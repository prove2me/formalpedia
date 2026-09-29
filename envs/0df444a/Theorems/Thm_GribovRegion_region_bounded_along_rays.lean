-- Prove2me | Theorems.Thm_GribovRegion_region_bounded_along_rays
-- name    : GribovRegion.region_bounded_along_rays
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:19:44.406472+00:00
-- url     : https://prove2.me/theorems/5c78a56e-450f-473b-be69-6ba4d373187d
-- title:
--   Eq. (2.59): $\Omega$ is bounded in every direction
-- statement:
--   For a configuration $A$ whose field-dependent part $M_2(A)$ is nonzero, the rescaled configurations $\lambda A$ leave the Gribov region once $\lambda$ is large enough: choosing $\omega$ with $\omega^{\mathsf T} M_2(A)\,\omega = \kappa < 0$ gives
--
--   $$ \omega^{\mathsf T} M(\lambda A)\, \omega = \omega^{\mathsf T} M_0\, \omega + \lambda \kappa, $$
--
--   which is negative for $\lambda$ large. This is Eq. (2.59) and the fourth property listed on p. 189 of the review: $\Omega$ is bounded in every direction.
-- source:
--   N. Vandersickel, D. Zwanziger, The Gribov problem and QCD dynamics, Physics Reports 520 (2012) 175-251, doi:10.1016/j.physrep.2012.07.003, Section 2.2.1 (pp. 188-189), Eqs. (2.52)-(2.59)

import Definitions.Def_gribov_region_model

set_option autoImplicit false

namespace GribovRegion

theorem region_bounded_along_rays {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) (A : V) (hA : m.lin A ≠ 0) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, l₀ ≤ l → l • A ∉ region m := by sorry

end GribovRegion
