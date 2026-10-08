-- Prove2me | Theorems.Thm_GenericBudgets_IdenticalPrefs_identical_all_po_no_anti
-- name    : GenericBudgets.IdenticalPrefs.identical_all_po_no_anti
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:06.373643+00:00
-- url     : https://prove2.me/theorems/b62b857f-03a9-4f82-b705-1f68b291cbaf
-- title:
--   §8, p. 20 — with identical preferences every allocation is PO and none is anti-proportional
-- statement:
--   Consider two agents with the *same* standard (additive, normalized, non-negative, monotone, strict) valuation $v_1 = v_2$ and positive budgets $b_1, b_2$ with $b_1 + b_2 = 1$. Then
--
--   1. every allocation is Pareto optimal, and
--   2. no allocation is anti-proportional:
--   $$\text{there is no allocation } \mathcal S \text{ with } v_i(\mathcal S_i) \le b_i \text{ for both } i \text{ and } v_i(\mathcal S_i) < b_i \text{ for some } i.$$
--
--   With a common additive normalized valuation the two values always add up to $1 = b_1 + b_2$ ("constant-sum game"): whatever one agent gains the other loses. This is the observation that reduces Theorem 8.1 to Lemma 8.2.
--
--   **Formalization Note** Agents are indexed $0, 1$. Identical preferences are the hypothesis `v 0 = v 1`. The page's sentence says "at most their truncated share"; the definition of anti-proportionality (p. 12), which the sentence refers to, uses the budget-proportional share, and that is what is stated. Strictness (without the identical-items exception) is needed for the first claim: with ties, two different allocations can give both agents the same values.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 20, §8, paragraph after Theorem 8.1

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.IdenticalPrefs

theorem identical_all_po_no_anti {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, GenericBudgets.AlmostEqual.IsStandardValuation (v i)) (hsame : v 0 = v 1)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1) :
    (∀ σ, GenericBudgets.AlmostEqual.IsPO v σ) ∧ ∀ σ, ¬ GenericBudgets.AlmostEqual.IsAntiProportional v b σ := by sorry

end GenericBudgets.IdenticalPrefs
