-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_necessity_gt_simplex
-- name    : Grunbaum2003.g_theorem_necessity_gt_simplex
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-09T01:27:44.103842+00:00
-- url     : https://prove2.me/theorems/5df4e894-07a1-4182-be07-949dac794676
-- title:
--   Stanley necessity theorem for simplicial d-polytopes with more than d + 1 vertices (d ≥ 4)
-- statement:
--   For every dimension $d \ge 4$ and every simplicial $d$-polytope $P \subseteq \mathbb{R}^d$ (`IsSimplicialDPolytope P`) with strictly more than $d + 1$ vertices ($f_0(P) > d + 1$), there exists an $M$-sequence $g : \mathbb{N} \to \mathbb{N}$ of length $\lfloor d/2 \rfloor$ (`IsMSequence (d / 2) g`) such that
--
--   $$f_j(P) = \sum_{i=0}^{\lfloor d/2 \rfloor} g(i)\, M_d(i, j + 1) \qquad (0 \le j < d).$$
--
--   **Formalization Note** Combined with the $d$-simplex case $f_0(P) \le d + 1$ proved in `g_theorem_simplex_and_zero_tail_characterization`, this yields `g_theorem_necessity`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §10.6, pp. 198a–198b / PDF pp. 235–236 (citing R. P. Stanley 1980)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_necessity_gt_simplex (d : ℕ) (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (hP : IsSimplicialDPolytope P) (hV_gt : d + 1 < faceCount P 0) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by sorry

end Grunbaum2003
