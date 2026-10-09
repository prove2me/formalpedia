-- Prove2me | Theorems.Thm_OnlineCRS_Knapsack_knapsack_ocrs
-- name    : OnlineCRS.Knapsack.knapsack_ocrs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:24.428986+00:00
-- url     : https://prove2.me/theorems/42165372-0318-4927-9ba6-74c4ab33de2d
-- title:
--   Theorem 2.9 — randomized greedy OCRS for a knapsack polytope
-- statement:
--   Let $N$ be a finite ground set. Every element has a size $s_e\in[0,1]$, and let $P=\{x\in[0,1]^N:\sum_{e\in N}s_ex_e\le1\}$ be the natural unit-capacity knapsack polytope. For every $b\in[0,1/2]$, there exists a randomized greedy OCRS for $P$ whose selectability parameter is
--
--   $$c=\frac{1-2b}{2-2b}.$$
--
--   Thus, for every $x\in bP$ and every element $e$, the probability that $e$ is selectable, over the independent active set and random greedy-family choice, is at least $c$.
--
--   This is the knapsack result in Theorem 1.8 and the main target of this mission.
--
--   **Formalization Note** A greedy family contains the empty set, and the polytope includes the box constraints. At $b=1/2$, the guaranteed probability is zero; the denominator is at least one throughout the stated domain.
-- source:
--   arXiv:1508.00142v2, Theorem 2.9, p. 14; Theorem 1.8, p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Knapsack_Model

namespace OnlineCRS.Knapsack

/-- Theorem 2.9, p. 14: the natural knapsack relaxation admits a randomized greedy
OCRS with selectability `(1-2b)/(2-2b)` for `b ∈ [0,1/2]`. -/
theorem knapsack_ocrs {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) :
    ∃ w : (α → ℝ) → Finset (Finset α) → ℝ,
      OnlineCRS.Matroid.IsSelectableRand (knapsackFeasible s) (knapsackPolytope s)
        b ((1 - 2 * b) / (2 - 2 * b)) w := by sorry

end OnlineCRS.Knapsack
