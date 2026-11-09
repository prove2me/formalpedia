-- Prove2me | Theorems.Thm_Grunbaum2003_polygon_edge_count_eq_vertex_count
-- name    : Grunbaum2003.polygon_edge_count_eq_vertex_count
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T20:49:28.644135+00:00
-- url     : https://prove2.me/theorems/9c7ea45a-b452-4fae-9fe9-8a1558e3816a
-- title:
--   Euler's relation for polygons: $f_1(P)=f_0(P)$
-- statement:
--   Let $P\subseteq\mathbb R^2$ be a convex polygon, i.e. a $2$-dimensional polytope. Then $P$ has as many edges as vertices:
--
--   $$
--   f_1(P)=f_0(P).
--   $$
--
--   This is the case $d=2$ of Euler's relation $\sum_{i=0}^{d-1}(-1)^i f_i(P)=1-(-1)^d$, and it is the $d=2$ part of the characterisation of $f$-vectors in the $g$-theorem.
--
--   **Formalization Note** A $d$-polytope is a nonempty finite convex hull in $\mathbb R^d$ (`Fin d → ℝ`) with full affine span (`IsDPolytope`); faces are exposed subsets, and $f_k(P)$ (`faceCount P k`) counts nonempty exposed faces whose affine span has a $k$-dimensional direction.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §8.1, Theorem 8.1.1 (Euler's relation), case d = 2; used in §10.6, pp. 198a–198b (g-theorem, d = 2)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount

set_option autoImplicit false

namespace Grunbaum2003

theorem polygon_edge_count_eq_vertex_count (P : Set (Fin 2 → ℝ)) (hP : IsDPolytope P) :
    faceCount P 1 = faceCount P 0 := by sorry

end Grunbaum2003
