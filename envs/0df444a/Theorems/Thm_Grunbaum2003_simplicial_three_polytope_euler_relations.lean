-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_three_polytope_euler_relations
-- name    : Grunbaum2003.simplicial_three_polytope_euler_relations
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T20:49:23.574296+00:00
-- url     : https://prove2.me/theorems/40efabb0-3c23-4a65-8bcd-1dafb8e4d635
-- title:
--   Euler and Dehn–Sommerville relations for simplicial $3$-polytopes
-- statement:
--   Let $P\subseteq\mathbb R^3$ be a simplicial $3$-polytope, i.e. every facet of $P$ is a triangle. Write $f_0,f_1,f_2$ for the numbers of vertices, edges and facets. Then
--
--   1. (Euler's relation) $f_0-f_1+f_2=2$, written as $f_0+f_2=f_1+2$;
--   2. (Dehn–Sommerville relation) $3f_2=2f_1$.
--
--   Together these give the $d=3$ necessity part of the $g$-theorem: $f_1=3f_0-6$ and $f_2=2f_0-4$.
--
--   **Formalization Note** A $d$-polytope is a nonempty finite convex hull in $\mathbb R^d$ (`Fin d → ℝ`) with full affine span (`IsDPolytope`); faces are exposed subsets, and $f_k(P)$ (`faceCount P k`) counts nonempty exposed faces whose affine span has a $k$-dimensional direction. `IsSimplicialDPolytope` requires every nonempty exposed face of dimension $d-1$ to be the convex hull of $d$ affinely independent points.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §8.1, Theorem 8.1.1 (Euler's relation, d = 3) and §9.2 (Dehn–Sommerville equations, d = 3); used in §10.6, pp. 198a–198b (g-theorem, d = 3)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount

set_option autoImplicit false

namespace Grunbaum2003

theorem simplicial_three_polytope_euler_relations (P : Set (Fin 3 → ℝ))
    (hP : IsSimplicialDPolytope P) :
    faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 ∧
      3 * faceCount P 2 = 2 * faceCount P 1 := by sorry

end Grunbaum2003
