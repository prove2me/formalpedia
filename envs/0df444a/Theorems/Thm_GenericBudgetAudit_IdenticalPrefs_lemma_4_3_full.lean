-- Prove2me | Theorems.Thm_GenericBudgetAudit_IdenticalPrefs_lemma_4_3_full
-- name    : GenericBudgetAudit.IdenticalPrefs.lemma_4_3_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:31:32.766022+00:00
-- url     : https://prove2.me/theorems/2601c1ad-f625-45f2-8aeb-87b423d08c3c
-- title:
--   Lemma 4.3 — budget-exhausting combination pricing is sufficient
-- statement:
--   Let two agents have nonnegative normalized additive valuations, positive normalized budgets $b_1\ge b_2>0$, and an efficient allocation $S$. Suppose the given prices satisfy $p_j=\alpha v_1(\{j\})+\beta v_2(\{j\})$, where $\alpha,\beta\ge0$ and $\max\{\alpha,\beta\}>0$, and exhaust both budgets. Then
--
--   $$
--   (S,p)\text{ is a competitive equilibrium}.
--   $$
--
--   The allocation and prices in the conclusion are the supplied ones. Equal budgets are allowed. This gives a sufficient pricing criterion for efficient additive allocations.
--
--   Differences from the source:
--   - reading: PO allocations distinguished by allocation equality, with identical-item interchangeability → efficiency and equality of frontier points use attained utility vectors; reason: pp. 6, 7, 13 and 15 allow interchangeable identical items and require strictly ordered frontier levels; two items valued 1/2 by both agents give different labelled assignments with the same efficient vector
--   - generalization: strict preferences and strict inclusion monotonicity apart from identical items → nonnegative normalized additive valuations with arbitrary ties and zero-value goods; reason: every source additive market satisfies this weaker valuation predicate; no source instance is removed and the demand domain remains all bundles
--   - encoding: finite item set M and agents 1 and 2 → items Fin m, agents Fin 2 indexed 0 and 1, allocations total item-to-agent functions; reason: finite relabelling preserves every bundle and clearing partition, including empty bundles
--   - encoding: definitions shared across the paper → concrete theorem-local lets copied from the staged Model definition; reason: each draft must compile independently and cannot import another unpublished draft; the lets add no hypotheses or free predicates
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2 (2018), Lemma 4.3, p. 11. https://arxiv.org/abs/1703.08150v2

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

open scoped Classical
open GenericBudgets.AlmostEqual (bundle price IsCE)

noncomputable section

namespace GenericBudgetAudit.IdenticalPrefs

/-- Self-contained draft: concrete local lets duplicate Model, because drafts cannot import drafts. -/
theorem lemma_4_3_full {m : ℕ} :
  let IsAdditive (w : Finset (Fin m) → ℝ) : Prop :=
    (∀ j, 0 ≤ w {j}) ∧ (∀ S, w S = ∑ j ∈ S, w {j}) ∧ w Finset.univ = 1;
  let IsBudgets (b : Fin 2 → ℝ) : Prop :=
    (∀ i, 0 < b i) ∧ b 0 + b 1 = 1;
  let Efficient (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2) : Prop :=
    ∀ τ : Fin m → Fin 2, (∀ i, v i (bundle σ i) ≤ v i (bundle τ i)) →
      ∀ i, v i (bundle τ i) = v i (bundle σ i);
  let Exhausting (b : Fin 2 → ℝ) (σ : Fin m → Fin 2) (p : Fin m → ℝ) : Prop :=
    ∀ i, price p (bundle σ i) = b i;
  let CombinationPricing (v : Fin 2 → Finset (Fin m) → ℝ) (p : Fin m → ℝ) : Prop :=
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 < max α β ∧
      ∀ j, p j = α * v 0 {j} + β * v 1 {j};
  ∀ (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (σ : Fin m → Fin 2) (p : Fin m → ℝ),
    (∀ i, IsAdditive (v i)) → IsBudgets b → b 1 ≤ b 0 →
    Efficient v σ → CombinationPricing v p → Exhausting b σ p → IsCE v b σ p := by sorry

end GenericBudgetAudit.IdenticalPrefs
