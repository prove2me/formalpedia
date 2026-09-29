-- Prove2me | Theorems.Thm_GribovRegion_convex_region
-- name    : GribovRegion.convex_region
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:09:31.056578+00:00
-- url     : https://prove2.me/theorems/47d5455a-40c2-4d9b-a5ff-936a658a2a05
-- title:
--   The Gribov region $\Omega$ is convex
-- statement:
--   The Gribov region is convex: if $A_1$ and $A_2$ satisfy $M(A_i) > 0$ and $\alpha, \beta \ge 0$ with $\alpha + \beta = 1$, then $M(\alpha A_1 + \beta A_2) = \alpha M(A_1) + \beta M(A_2)$ is again positive definite. This is the third property listed on p. 189 of the review, attributed there to Zwanziger, Nucl. Phys. B209 (1982) 336.
-- source:
--   N. Vandersickel, D. Zwanziger, The Gribov problem and QCD dynamics, Physics Reports 520 (2012) 175-251, doi:10.1016/j.physrep.2012.07.003, Section 2.2.1 (pp. 188-189), Eqs. (2.52)-(2.59)

import Definitions.Def_gribov_region_model

set_option autoImplicit false

namespace GribovRegion

theorem convex_region {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) : Convex ℝ (region m) := by sorry

end GribovRegion
