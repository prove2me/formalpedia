-- Prove2me | Theorems.Thm_GribovRegion_fpOperator_convex_comb
-- name    : GribovRegion.fpOperator_convex_comb
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T17:58:58.886018+00:00
-- url     : https://prove2.me/theorems/f8c51738-b00e-4241-ba1b-ae751a158443
-- title:
--   Eq. (2.53): $M(\alpha A_1 + \beta A_2) = \alpha M(A_1) + \beta M(A_2)$
-- statement:
--   The Faddeev--Popov operator depends affinely on the gauge field: for real numbers $\alpha, \beta$ with $\alpha + \beta = 1$ and configurations $A_1, A_2$,
--
--   $$ M(\alpha A_1 + \beta A_2) = \alpha M(A_1) + \beta M(A_2). $$
--
--   This is the identity displayed in the review just below Eq. (2.53), and it is the algebraic input to the convexity of the Gribov region.
-- source:
--   N. Vandersickel, D. Zwanziger, The Gribov problem and QCD dynamics, Physics Reports 520 (2012) 175-251, doi:10.1016/j.physrep.2012.07.003, Section 2.2.1 (pp. 188-189), Eqs. (2.52)-(2.59)

import Definitions.Def_gribov_region_model

set_option autoImplicit false

namespace GribovRegion

theorem fpOperator_convex_comb {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) (a b : ℝ) (hab : a + b = 1) (A₁ A₂ : V) :
    fpOperator m (a • A₁ + b • A₂) = a • fpOperator m A₁ + b • fpOperator m A₂ := by sorry

end GribovRegion
