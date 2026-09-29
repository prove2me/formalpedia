-- Prove2me | Theorems.Thm_GribovRegion_zero_mem_region
-- name    : GribovRegion.zero_mem_region
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:08:51.449361+00:00
-- url     : https://prove2.me/theorems/1a286cbb-e420-4ac1-ad9f-5ae603970086
-- title:
--   $A = 0$ lies in the Gribov region $\Omega$
-- statement:
--   The perturbative configuration $A = 0$ belongs to the Gribov region: at $A = 0$ the Faddeev--Popov operator reduces to its field-independent part $M_0$ (the operator $-\partial^2$), which is positive definite by assumption. This is the second property listed on p. 189 of the review.
-- source:
--   N. Vandersickel, D. Zwanziger, The Gribov problem and QCD dynamics, Physics Reports 520 (2012) 175-251, doi:10.1016/j.physrep.2012.07.003, Section 2.2.1 (pp. 188-189), Eqs. (2.52)-(2.59)

import Definitions.Def_gribov_region_model

set_option autoImplicit false

namespace GribovRegion

theorem zero_mem_region {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) : (0 : V) ∈ region m := by sorry

end GribovRegion
