-- Prove2me | Theorems.Thm_Grunbaum2003_boundary_refines_simplex_pos_dim
-- name    : Grunbaum2003.boundary_refines_simplex_pos_dim
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:39.612675+00:00
-- url     : https://prove2.me/theorems/f8ce796b-bb7b-4487-85bc-ecf8fe200d92
-- title:
--   Boundary refinement of a $d$-simplex by any $d$-polytope in positive dimension ($d \ge 1$)
-- statement:
--   This theorem states the positive-dimension case ($d \ge 1$) of Grünbaum's Theorem 11.1.1: for every $d \ge 1$, the boundary complex $\mathcal{B}(P)$ of any $d$-polytope $P \subseteq \mathbb{R}^d$ is a refinement of the boundary complex $\mathcal{B}(T^d)$ of any $d$-simplex $T^d = \operatorname{conv}(\operatorname{range} v) \subseteq \mathbb{R}^d$.
--
--   Let $d \ge 1$ be a positive integer, let $P \subseteq \mathbb{R}^d$ be a $d$-polytope (`IsDPolytope P`), and let $v : \operatorname{Fin}(d + 1) \to \mathbb{R}^d$ be an affinely independent family of $d + 1$ vertices (`AffineIndependent ℝ v`). Then
--
--   $$
--   \operatorname{BoundaryRefines}\bigl(P,\, \operatorname{conv}(\operatorname{range} v)\bigr).
--   $$
--
--   Together with `boundary_refines_simplex_zero_dim` (which proves the degenerate $d = 0$ case where both boundary carriers are empty), this theorem establishes `boundary_refines_simplex` for all $d \in \mathbb{N}$ by case analysis on $d = 0$ vs. $d > 0$.
--
--   **Formalization Note** In dimension $d \ge 1$, both $P$ and $T^d$ have nonempty interior in $\mathbb{R}^d$, and radial projection from a common interior point (after a projective transformation placing an interior point of $T^d$ strictly inside a facet cone of $P$, as in Grünbaum §11.1, p. 200) provides a piecewise-projective homeomorphism $\partial P \xrightarrow{\sim} \partial T^d$ carrying subcomplexes of $\mathcal{B}(P)$ onto each proper face of $T^d$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §11.1, p. 200, Theorem 11.1.1

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false

namespace Grunbaum2003

theorem boundary_refines_simplex_pos_dim (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin (d + 1) → (Fin d → ℝ)) (hv : AffineIndependent ℝ v) :
    BoundaryRefines P (convexHull ℝ (Set.range v)) := by sorry

end Grunbaum2003
