-- Prove2me | Theorems.Thm_NarrowDNF_Weighted_select_two_budgets
-- name    : NarrowDNF.Weighted.select_two_budgets
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:34.733206+00:00
-- url     : https://prove2.me/theorems/6edf4289-829a-4c0c-aa72-9ee34f1adefb
-- title:
--   Simultaneous deterministic selection of error and cost budgets
-- statement:
--   Let $A$ be nonempty and finite with strictly positive normalized weights $w$. Let $E,C:A\to[0,\infty)$, and assume $\sum_xw(x)E(x)\le e$ and $\sum_xw(x)C(x)\le B$, where $B\ge0$. For every $\tau>0$,
--   $$
--   \exists x:\quad E(x)\le e+\tau,\qquad C(x)\le B\left(1+\frac e\tau\right).
--   $$
--   The conclusion includes $B=0$. It chooses one realization controlling both the approximation error and the active-set cost, instead of selecting these two quantities separately.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Weighted.lean#L53-L99

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_NarrowDNF_Weighted_exists_le_mean

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Weighted
end NarrowDNF.Weighted
open NarrowDNF
open NarrowDNF
open NarrowDNF.Weighted
open scoped BigOperators
variable {α : Type*} [Fintype α]

theorem NarrowDNF.Weighted.select_two_budgets [Nonempty α] (weights : α → ℝ)
    (hw : ∀ x, 0 < weights x) (hs : ∑ x, weights x = 1)
    (err cost : α → ℝ) (herr : ∀ x, 0 ≤ err x) (hcost : ∀ x, 0 ≤ cost x)
    (e B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ)
    (he : (∑ x, weights x * err x) ≤ e)
    (hM : (∑ x, weights x * cost x) ≤ B) :
    ∃ x, err x ≤ e + τ ∧ cost x ≤ B * (1 + e / τ) := by sorry
