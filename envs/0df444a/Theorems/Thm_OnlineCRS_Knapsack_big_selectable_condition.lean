-- Prove2me | Theorems.Thm_OnlineCRS_Knapsack_big_selectable_condition
-- name    : OnlineCRS.Knapsack.big_selectable_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:04.953068+00:00
-- url     : https://prove2.me/theorems/4d87d7ba-2598-4574-8222-0c9270a559b8
-- title:
--   Display (3) — sufficient condition for a big element to be selectable
-- statement:
--   Let $e$ be a big element, so $s_e>1/2$, and let $A$ be a realized active set. If the total size of the other big elements in $A$ is at most $1-s_e$, then $e$ is selectable in the big-element greedy family:
--
--   $$\sum_{f\in(A\cap N_{\mathrm{big}})\setminus\{e\}}s_f\le1-s_e\quad\Longrightarrow\quad e\text{ is selectable for }(A,F_{\mathrm{big}}).$$
--
--   This is the pointwise implication behind the probability lower bound in display (3).
--
--   **Formalization Note** The printed sum in display (3) includes $e$. The next displayed equality removes $e$; the corrected exclusion is used here, as recorded in the moderation notes.
-- source:
--   arXiv:1508.00142v2, proof of Theorem 2.9, display (3) and following paragraph, p. 15

import Mathlib
import Definitions.Def_OnlineCRS_Knapsack_Model

namespace OnlineCRS.Knapsack

/-- The sufficient condition used at display (3), p. 15, with the tested element removed
from the load as required by the equality in the next display. -/
theorem big_selectable_condition {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (A : Finset α) (e : α) (he : e ∈ bigElements s)
    (hload : ∑ f ∈ ((A ∩ bigElements s).erase e), s f ≤ 1 - s e) :
    OnlineCRS.Matroid.Selectable (bigFamily s) A e := by sorry

end OnlineCRS.Knapsack
