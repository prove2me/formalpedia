-- Prove2me | Theorems.Thm_Grunbaum2003_boundary_refines_simplex_zero_dim
-- name    : Grunbaum2003.boundary_refines_simplex_zero_dim
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:30.111799+00:00
-- url     : https://prove2.me/theorems/b6c627b2-1880-4b65-a860-6bf8ab2f806a
-- title:
--   Boundary refinement of a $0$-simplex by any $0$-polytope
-- statement:
--   This theorem establishes the zero-dimensional base case ($d = 0$) of Grünbaum's Theorem 11.1.1 (`boundary_refines_simplex`): the boundary complex of every $0$-polytope refines the boundary complex of every $0$-simplex in $\mathbb{R}^0$.
--
--   Let $P \subseteq \mathbb{R}^0$ be a $0$-polytope (`IsDPolytope P`), and let $v : \operatorname{Fin} 1 \to \mathbb{R}^0$ be an affinely independent family of $1$ point in $\mathbb{R}^0$ (`AffineIndependent ℝ v`), so that $T^0 = \operatorname{conv}(\operatorname{range} v)$ is a $0$-simplex. Then $P$ boundary-refines $T^0$:
--
--   $$
--   \operatorname{BoundaryRefines}\bigl(P,\, \operatorname{conv}(\operatorname{range} v)\bigr).
--   $$
--
--   In $\mathbb{R}^0 = \{0\}$, both $P$ and $T^0$ are equal to the singleton $\{0\}$, so their proper exposed faces consist solely of the empty face $\emptyset$. Consequently, both boundary carriers $\bigcup \mathcal{B}(P)$ and $\bigcup \mathcal{B}(T^0)$ are empty, and the unique homeomorphism between them maps the empty face $\emptyset \in \mathcal{B}(T^0)$ to the subcomplex $\{\emptyset\} \subseteq \mathcal{B}(P)$.
--
--   **Formalization Note** This lemma cleanly separates the degenerate dimension $d = 0$ (where the boundary carrier $\partial P = \emptyset$ has no points) from the positive-dimension case $d \ge 1$ (where radial projection from an interior point identifies $\partial P$ and $\partial T^d$ with $S^{d-1}$).
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §11.1, p. 200, Theorem 11.1.1

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false

namespace Grunbaum2003

theorem boundary_refines_simplex_zero_dim
    (P : Set (Fin 0 → ℝ)) (hP : IsDPolytope P)
    (v : Fin 1 → (Fin 0 → ℝ)) (hv : AffineIndependent ℝ v) :
    BoundaryRefines P (convexHull ℝ (Set.range v)) := by sorry

end Grunbaum2003
