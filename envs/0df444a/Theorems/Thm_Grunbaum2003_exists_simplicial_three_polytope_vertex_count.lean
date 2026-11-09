-- Prove2me | Theorems.Thm_Grunbaum2003_exists_simplicial_three_polytope_vertex_count
-- name    : Grunbaum2003.exists_simplicial_three_polytope_vertex_count
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T20:49:31.993609+00:00
-- url     : https://prove2.me/theorems/698f0319-9a1d-4ee0-9302-9a802b194518
-- title:
--   Existence of a simplicial $3$-polytope with $n+4$ vertices
-- statement:
--   For every natural number $n$ there is a simplicial $3$-polytope $P\subseteq\mathbb R^3$ with exactly $n+4$ vertices:
--
--   $$
--   \forall n\in\mathbb N\ \exists P \text{ simplicial}:\quad f_0(P)=n+4 .
--   $$
--
--   This is the realisability half of the $d=3$ case of the $g$-theorem. The cyclic polytope $C(n+4,3)$, the convex hull of $n+4$ points on the moment curve $t\mapsto(t,t^2,t^3)$, is an example.
--
--   **Formalization Note** A $d$-polytope is a nonempty finite convex hull in $\mathbb R^d$ (`Fin d → ℝ`) with full affine span (`IsDPolytope`); faces are exposed subsets, and $f_k(P)$ (`faceCount P k`) counts nonempty exposed faces whose affine span has a $k$-dimensional direction. `IsSimplicialDPolytope` requires every nonempty exposed face of dimension $d-1$ to be the convex hull of $d$ affinely independent points.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §4.7 (cyclic polytopes C(v,d) are simplicial with v vertices), case d = 3; used in §10.6, pp. 198a–198b (g-theorem, d = 3)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_simplicial_three_polytope_vertex_count (n : ℕ) :
    ∃ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P ∧ faceCount P 0 = n + 4 := by sorry

end Grunbaum2003
