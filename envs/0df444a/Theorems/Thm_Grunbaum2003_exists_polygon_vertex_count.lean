-- Prove2me | Theorems.Thm_Grunbaum2003_exists_polygon_vertex_count
-- name    : Grunbaum2003.exists_polygon_vertex_count
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T20:49:29.38642+00:00
-- url     : https://prove2.me/theorems/48a8f5a1-9294-460b-a13f-661b5dcc6af9
-- title:
--   Existence of an $(n+3)$-gon
-- statement:
--   For every natural number $n$ there is a convex polygon $P\subseteq\mathbb R^2$ with exactly $n+3$ vertices:
--
--   $$
--   \forall n\in\mathbb N\ \exists P:\quad f_0(P)=n+3 .
--   $$
--
--   This is the realisability half of the $d=2$ case of the $g$-theorem; a cyclic polygon (the convex hull of $n+3$ points on the parabola $y=x^2$) is an example.
--
--   **Formalization Note** A $d$-polytope is a nonempty finite convex hull in $\mathbb R^d$ (`Fin d → ℝ`) with full affine span (`IsDPolytope`); faces are exposed subsets, and $f_k(P)$ (`faceCount P k`) counts nonempty exposed faces whose affine span has a $k$-dimensional direction.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §4.7 (cyclic polytopes C(v,d), case d = 2); used in §10.6, pp. 198a–198b (g-theorem, d = 2)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_polygon_vertex_count (n : ℕ) :
    ∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧ faceCount P 0 = n + 3 := by sorry

end Grunbaum2003
