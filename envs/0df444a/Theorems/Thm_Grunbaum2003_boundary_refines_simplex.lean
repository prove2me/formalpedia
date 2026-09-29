-- Prove2me | Theorems.Thm_Grunbaum2003_boundary_refines_simplex
-- name    : Grunbaum2003.boundary_refines_simplex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:40:00.158066+00:00
-- url     : https://prove2.me/theorems/dcd75ce3-e5c0-43f4-a5f7-60250f82c7bc
-- title:
--   Theorem 11.1.1 — Every polytope boundary refines a simplex boundary
-- statement:
--   For every full-dimensional d-polytope P and every d-simplex given by d+1 affinely independent vertices, the boundary complex of P refines the boundary complex of that simplex.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §11.1, Theorem 11.1.1, printed p. 200 / PDF p. 240; definitions printed p. 199 / PDF p. 239; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), §11.1, Theorem 1 (11.1.1), printed p.200 / PDF240:
every d-polytope boundary complex is a refinement of the d-simplex boundary.
The target simplex is arbitrary, represented by d+1 affinely independent
vertices in real d-space. The map and all face-preimage conditions use the
same homeomorphism. No simpliciality assumption is made on P, and the
zero-dimensional case retains the empty boundary carrier. Statement only. -/
theorem boundary_refines_simplex (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin (d + 1) → (Fin d → ℝ)) (hv : AffineIndependent ℝ v) :
    BoundaryRefines P (convexHull ℝ (Set.range v)) := by sorry

end Grunbaum2003
