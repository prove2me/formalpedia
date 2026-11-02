-- Prove2me | Theorems.Thm_Grunbaum2003_boundary_refines_simplex_one_dim
-- name    : Grunbaum2003.boundary_refines_simplex_one_dim
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:03:46.150502+00:00
-- url     : https://prove2.me/theorems/0f92d039-c68d-4951-ba16-3a30890b7e99
-- title:
--   Boundary refinement of one-dimensional polytopes
-- statement:
--   Let $P$ be a nonempty full-dimensional polytope in real one-dimensional coordinate space, and let $v_0,v_1$ be an affinely independent pair. Then
--
--   $$\mathcal B(P)\text{ refines }\mathcal B(\operatorname{conv}\{v_0,v_1\}).$$
--
--   Refinement means a homeomorphism of boundary carriers whose inverse image of each target face is a finite union of source faces forming a subcomplex. This is the one-dimensional base case of Grünbaum’s boundary-refinement theorem.
-- source:
--   Grünbaum (2003), Convex Polytopes, §11.1, Theorem 11.1.1, printed p.199 / PDF239, specialized to dimension one; Branko Grünbaum, On the facial structure of convex polytopes (1965), boundary-refinement theorem. https://faculty.washington.edu/moishe/branko/BG52.Facial%20structure.pdf

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Grunbaum2003

theorem boundary_refines_simplex_one_dim
    (P : Set (Fin 1 → ℝ)) (hP : IsDPolytope P)
    (v : Fin 2 → (Fin 1 → ℝ)) (hv : AffineIndependent ℝ v) :
    BoundaryRefines P (convexHull ℝ (Set.range v)) := by sorry

end Grunbaum2003
