-- Prove2me | Theorems.Thm_Grunbaum2003_exists_stacked_simplicial_polytope_faceCount
-- name    : Grunbaum2003.exists_stacked_simplicial_polytope_faceCount
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-09T01:53:47.241167+00:00
-- url     : https://prove2.me/theorems/92e559a0-fba2-4b8d-b1c2-526965d16275
-- title:
--   Realization of stacked simplicial $d$-polytope face vectors
-- statement:
--   For every dimension $d \ge 4$ and positive integer $n > 0$, there exists a simplicial $d$-polytope $P \subset \mathbb{R}^d$ whose face counts $f_j(P)$ ($0 \le j < d$) are given by the stacked-polytope formula:
--
--   $$
--   f_j(P) = \binom{d+1}{j+1} + n\,M_{d,1,j+1}.
--   $$
--
--   This realizes the $g(2) = 0$ branch of the $g$-theorem sufficiency proof by iterated stellar subdivision (stacking) of a $d$-simplex.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed.), §10.6, pp. 198a–198b (PDF 235–236)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_stacked_simplicial_polytope_faceCount (d : ℕ) (hd : 4 ≤ d)
    (n : ℕ) (hn : 0 < n) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        (Nat.choose (d + 1) j.succ.val : ℤ) + (n : ℤ) * gTheoremMatrix d 1 j.succ.val := by sorry

end Grunbaum2003
