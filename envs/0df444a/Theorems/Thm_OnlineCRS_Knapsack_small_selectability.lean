-- Prove2me | Theorems.Thm_OnlineCRS_Knapsack_small_selectability
-- name    : OnlineCRS.Knapsack.small_selectability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:48.049039+00:00
-- url     : https://prove2.me/theorems/3f455477-0e00-4613-ac64-f05120b4d1be
-- title:
--   Proof of Theorem 2.9 — selectability bound for small elements
-- statement:
--   For sizes $s_e\in[0,1]$, $b\in[0,1/2]$, $x\in bP$, and each small element $e\notin N_{\mathrm{big}}$, the paper's randomized big/small greedy family satisfies
--
--   $$\Pr[e\text{ is selectable}]\ge\frac{1-2b}{2-2b}.$$
--
--   This is the small-element half of the guarantee in Theorem 2.9; its bound uses the size threshold $1/2$.
-- source:
--   arXiv:1508.00142v2, proof of Theorem 2.9, small-element inequality chain, p. 15

import Mathlib
import Definitions.Def_OnlineCRS_Knapsack_Model

namespace OnlineCRS.Knapsack

open scoped Pointwise

/-- The small-element chain in the proof of Theorem 2.9, p. 15. -/
theorem small_selectability {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2)
    (x : α → ℝ) (hx : x ∈ b • knapsackPolytope s)
    (e : α) (he : e ∉ bigElements s) :
    (1 - 2 * b) / (2 - 2 * b) ≤
      ∑ Fam : Finset (Finset α), knapsackWeights s b x Fam * OnlineCRS.Matroid.selProb x Fam e := by sorry

end OnlineCRS.Knapsack
