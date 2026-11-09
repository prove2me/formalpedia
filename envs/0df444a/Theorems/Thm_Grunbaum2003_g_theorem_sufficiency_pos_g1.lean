-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_sufficiency_pos_g1
-- name    : Grunbaum2003.g_theorem_sufficiency_pos_g1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-09T01:27:46.251574+00:00
-- url     : https://prove2.me/theorems/f312b1bb-8a94-46e8-95fa-4915344e28cc
-- title:
--   Billera–Lee sufficiency theorem for M-sequences with positive g₁ (d ≥ 4)
-- statement:
--   For every dimension $d \ge 4$ and every $M$-sequence $g : \mathbb{N} \to \mathbb{N}$ of length $\lfloor d/2 \rfloor$ (`IsMSequence (d / 2) g`) with $g(1) > 0$, there exists a simplicial $d$-polytope $P \subseteq \mathbb{R}^d$ (`IsSimplicialDPolytope P`) whose face counts satisfy
--
--   $$f_j(P) = \sum_{i=0}^{\lfloor d/2 \rfloor} g(i)\, M_d(i, j + 1) \qquad (0 \le j < d).$$
--
--   **Formalization Note** Combined with the $g(1) = 0$ simplex case proved in `g_theorem_simplex_and_zero_tail_characterization`, this yields `g_theorem_sufficiency`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §10.6, pp. 198a–198b / PDF pp. 235–236 (citing L. J. Billera and C. W. Lee 1980, 1981)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_sufficiency_pos_g1 (d : ℕ) (hd : 4 ≤ d) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) (hg1 : 0 < g 1) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by sorry

end Grunbaum2003
