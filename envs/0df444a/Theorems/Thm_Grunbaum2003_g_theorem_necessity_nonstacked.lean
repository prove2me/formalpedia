-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_necessity_nonstacked
-- name    : Grunbaum2003.g_theorem_necessity_nonstacked
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T01:59:30.80892+00:00
-- url     : https://prove2.me/theorems/3515ba76-a67a-431f-ad1f-17a1c0ae58f6
-- title:
--   Necessity of the $g$-theorem for non-stacked simplicial $d$-polytopes ($d \ge 4$)
-- statement:
--   Let $d \ge 4$ and let $P \subset \mathbb{R}^d$ be a simplicial $d$-polytope with $f_0(P) > d + 1$ whose face vector is not given by the two-term stacked formula $\binom{d+1}{j+1} + (f_0(P) - (d+1))\,M_{d,1,j+1}$. Then there exists an $M$-sequence $g : \mathbb{N} \to \mathbb{N}$ of length $\lfloor d/2 \rfloor$ such that for all $0 \le j < d$,
--
--   $$
--   f_j(P) = \sum_{i=0}^{\lfloor d/2 \rfloor} g(i)\,M_{d,i,j+1}.
--   $$
--
--   Together with the simplex ($f_0(P) = d+1$) and stacked ($g(2) = 0$) cases, this completes the necessity direction of the $g$-theorem for $d \ge 4$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed.), §10.6, pp. 198a–198b (PDF 235–236)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_necessity_nonstacked (d : ℕ) (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (hP : IsSimplicialDPolytope P) (hV_gt : d + 1 < faceCount P 0)
    (hNonStacked : ¬ ∀ j : Fin d, (faceCount P j.val : ℤ) =
      (Nat.choose (d + 1) j.succ.val : ℤ) +
        ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by sorry

end Grunbaum2003
