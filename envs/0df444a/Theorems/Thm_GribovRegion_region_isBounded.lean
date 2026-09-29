-- Prove2me | Theorems.Thm_GribovRegion_region_isBounded
-- name    : GribovRegion.region_isBounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:28:12.875839+00:00
-- url     : https://prove2.me/theorems/194a1632-a7dd-40a7-bb68-0b758e485971
-- title:
--   The Gribov region $\Omega$ is a bounded set
-- statement:
--   When distinct configurations have distinct field-dependent parts, the Gribov region is bounded as a subset of a finite-dimensional normed configuration space. This is the qualitative form of the ellipsoidal containment of Dell'Antonio and Zwanziger, Nucl. Phys. B326 (1989) 333, quoted on p. 189 of the review; the explicit ellipsoid is not asserted here. The injectivity hypothesis is necessary: on the kernel of $A \mapsto M_2(A)$ the Faddeev--Popov operator does not change, so $\Omega$ would contain a whole linear subspace.
-- source:
--   N. Vandersickel, D. Zwanziger, The Gribov problem and QCD dynamics, Physics Reports 520 (2012) 175-251, doi:10.1016/j.physrep.2012.07.003, Section 2.2.1 (pp. 188-189), Eqs. (2.52)-(2.59)

import Definitions.Def_gribov_region_model

set_option autoImplicit false

namespace GribovRegion

theorem region_isBounded {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (m : FPModel V n)
    (hinj : Function.Injective m.lin) :
    Bornology.IsBounded (region m) := by sorry

end GribovRegion
