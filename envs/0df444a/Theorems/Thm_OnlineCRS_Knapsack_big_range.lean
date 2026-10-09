-- Prove2me | Theorems.Thm_OnlineCRS_Knapsack_big_range
-- name    : OnlineCRS.Knapsack.big_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:36.628459+00:00
-- url     : https://prove2.me/theorems/418e8598-d789-4b96-bbdd-85a0c193b47e
-- title:
--   Proof of Theorem 2.9 — range of the big load and mixing probability
-- statement:
--   Let $s_e\in[0,1]$ for every element, $b\in[0,1/2]$, and $x\in bP$ for the unit-capacity knapsack polytope. If $b_{\mathrm{big}}=\sum_{s_e>1/2}s_ex_e$ and $p_{\mathrm{big}}=(1-2b+2b_{\mathrm{big}})/(2-2b)$, then
--
--   $$0\le b_{\mathrm{big}}\le b,\qquad 0\le p_{\mathrm{big}}\le1.$$
--
--   The load bound is stated on page 14; the probability bound makes explicit that the construction's parameter is a valid mixing probability.
-- source:
--   arXiv:1508.00142v2, proof of Theorem 2.9, p. 14, paragraph after b_big display

import Mathlib
import Definitions.Def_OnlineCRS_Knapsack_Model

namespace OnlineCRS.Knapsack

open scoped Pointwise

/-- Proof of Theorem 2.9, p. 14: the big load lies in `[0,b]`; consequently the stated
mixing parameter is a probability on the theorem's domain. -/
theorem big_range {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2)
    (x : α → ℝ) (hx : x ∈ b • knapsackPolytope s) :
    0 ≤ bigLoad s x ∧ bigLoad s x ≤ b ∧
      0 ≤ bigProbability s b x ∧ bigProbability s b x ≤ 1 := by sorry

end OnlineCRS.Knapsack
