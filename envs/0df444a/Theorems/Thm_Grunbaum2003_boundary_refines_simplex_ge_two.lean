-- Prove2me | Theorems.Thm_Grunbaum2003_boundary_refines_simplex_ge_two
-- name    : Grunbaum2003.boundary_refines_simplex_ge_two
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:05:15.491003+00:00
-- url     : https://prove2.me/theorems/6aa0e05a-30f1-4e73-8905-e2c347ed89a4
-- title:
--   Boundary refinement of a simplex in dimension at least two
-- statement:
--   For every integer $d\ge 2$, every full-dimensional nonempty $d$-polytope $P\subseteq\mathbb R^d$, and every affinely independent family of $d+1$ target vertices $v$, the boundary complex of $P$ refines the boundary complex of the simplex spanned by $v$:
--
--   $$
--   \mathcal B(P)\text{ refines }\mathcal B(\operatorname{conv}(v)).
--   $$
--
--   Refinement means that a single homeomorphism between the two boundary carriers has the following property: the inverse image of each target boundary face is the carrier of a finite subcomplex of the source boundary, closed under exposed subfaces. The empty face is retained. No simpliciality assumption is imposed on $P$.
--
--   This is the dimension-at-least-two case of Grünbaum's boundary-refinement theorem. Together with the separately proved cases in dimensions zero and one, it gives the unrestricted theorem.
-- source:
--   Grünbaum, Convex Polytopes (2nd ed., 2003), §11.1, Theorem 11.1.1, printed p. 200 / PDF p. 240. Original inductive argument: Grünbaum, On the facial structure of convex polytopes (1965), Theorem 1*, pp. 559–560, https://faculty.washington.edu/moishe/branko/BG52.Facial%20structure.pdf

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false

namespace Grunbaum2003

theorem boundary_refines_simplex_ge_two (d : ℕ) (hd : 2 ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin (d + 1) → (Fin d → ℝ)) (hv : AffineIndependent ℝ v) :
    BoundaryRefines P (convexHull ℝ (Set.range v)) := by sorry

end Grunbaum2003
