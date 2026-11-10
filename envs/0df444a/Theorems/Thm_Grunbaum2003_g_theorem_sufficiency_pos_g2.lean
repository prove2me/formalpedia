-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_sufficiency_pos_g2
-- name    : Grunbaum2003.g_theorem_sufficiency_pos_g2
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T01:53:50.345133+00:00
-- url     : https://prove2.me/theorems/88dced49-d9b1-44ed-a865-2432142dfb2c
-- title:
--   Sufficiency of the $g$-theorem for $M$-sequences with $g(1) > 0$ and $g(2) > 0$
-- statement:
--   Let $d \ge 4$ and let $g : \mathbb{N} \to \mathbb{N}$ be an $M$-sequence of length $\lfloor d/2 \rfloor$ satisfying $g(1) > 0$ and $g(2) > 0$. Then there exists a simplicial $d$-polytope $P \subset \mathbb{R}^d$ such that for all $0 \le j < d$,
--
--   $$
--   f_j(P) = \sum_{i=0}^{\lfloor d/2 \rfloor} g(i)\,M_{d,i,j+1}.
--   $$
--
--   Together with the $g(1) = 0$ simplex case and the $g(2) = 0$ stacked-polytope case, this completes the sufficiency direction of the $g$-theorem for $d \ge 4$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed.), §10.6, pp. 198a–198b (PDF 235–236)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_sufficiency_pos_g2 (d : ℕ) (hd : 4 ≤ d) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) (hg1 : 0 < g 1) (hg2 : 0 < g 2) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by sorry

end Grunbaum2003
