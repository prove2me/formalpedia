-- Prove2me | Theorems.Thm_GenericBudgetAudit_IdenticalPrefs_lemma_5_5_full
-- name    : GenericBudgetAudit.IdenticalPrefs.lemma_5_5_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:32:24.093991+00:00
-- url     : https://prove2.me/theorems/27658985-9fe6-449a-ae1e-5550a943abd8
-- title:
--   Lemma 5.5 — the two fair frontier allocations coincide
-- statement:
--   Let two agents have nonnegative normalized additive valuations and arbitrary positive normalized budgets. Assume that no allocation is proportional and no efficient allocation is anti-proportional. For each ordered pair of distinct agents $i,k$, let $\check S^i$ minimize $i$'s efficient utility at or above $b_i$, and let $\hat S^k$ maximize $k$'s efficient utility at or below $b_k$. The assertion includes attainment and says
--
--   $$
--   \exists S\text{ efficient}:\quad v_i(S_i)=b_i^+,\quad v_k(S_k)=b_k^-,
--   \qquad [\check S^i]=[\hat S^k].
--   $$
--
--   Brackets denote utility vectors: every augmented minimizer for $i$ and every truncated maximizer for $k$ have the same two utilities. This identifies the two fair frontier points without identifying labelled bundles that differ by indifferent exchanges.
--
--   Differences from the source:
--   - reading: PO allocations distinguished by allocation equality, with identical-item interchangeability → efficiency and equality of frontier points use attained utility vectors; reason: pp. 6, 7, 13 and 15 allow interchangeable identical items and require strictly ordered frontier levels; two items valued 1/2 by both agents give different labelled assignments with the same efficient vector
--   - generalization: strict preferences and strict inclusion monotonicity apart from identical items → nonnegative normalized additive valuations with arbitrary ties and zero-value goods; reason: every source additive market satisfies this weaker valuation predicate; no source instance is removed and the demand domain remains all bundles
--   - encoding: finite item set M and agents 1 and 2 → items Fin m, agents Fin 2 indexed 0 and 1, allocations total item-to-agent functions; reason: finite relabelling preserves every bundle and clearing partition, including empty bundles
--   - encoding: the augmented and truncated optimizing allocations coincide up to interchangeable items → a common optimizing allocation exists and every two optimizing representatives have equal utilities for both agents; reason: attainment is stated explicitly and equality is equality of frontier points, without choosing arbitrary labelled representatives
--   - encoding: definitions shared across the paper → concrete theorem-local lets copied from the staged Model definition; reason: each draft must compile independently and cannot import another unpublished draft; the lets add no hypotheses or free predicates
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2 (2018), Lemma 5.5, p. 14. https://arxiv.org/abs/1703.08150v2

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

open scoped Classical
open GenericBudgets.AlmostEqual (bundle price IsCE)

noncomputable section

namespace GenericBudgetAudit.IdenticalPrefs

/-- Self-contained draft: concrete local lets duplicate Model, because drafts cannot import drafts. -/
theorem lemma_5_5_full {m : ℕ} :
  let IsAdditive (w : Finset (Fin m) → ℝ) : Prop :=
    (∀ j, 0 ≤ w {j}) ∧ (∀ S, w S = ∑ j ∈ S, w {j}) ∧ w Finset.univ = 1;
  let IsBudgets (b : Fin 2 → ℝ) : Prop :=
    (∀ i, 0 < b i) ∧ b 0 + b 1 = 1;
  let Efficient (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2) : Prop :=
    ∀ τ : Fin m → Fin 2, (∀ i, v i (bundle σ i) ≤ v i (bundle τ i)) →
      ∀ i, v i (bundle τ i) = v i (bundle σ i);
  let IsTruncMaximizer (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (i : Fin 2) (σ : Fin m → Fin 2) : Prop :=
    Efficient v σ ∧ v i (bundle σ i) ≤ b i ∧
      ∀ τ, Efficient v τ → v i (bundle τ i) ≤ b i → v i (bundle τ i) ≤ v i (bundle σ i);
  let IsAugMinimizer (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (i : Fin 2) (σ : Fin m → Fin 2) : Prop :=
    Efficient v σ ∧ b i ≤ v i (bundle σ i) ∧
      ∀ τ, Efficient v τ → b i ≤ v i (bundle τ i) → v i (bundle σ i) ≤ v i (bundle τ i);
  let Proportional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) : Prop :=
    ∀ i, b i ≤ v i (bundle σ i);
  let AntiProportional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) : Prop :=
    (∀ i, v i (bundle σ i) ≤ b i) ∧ ∃ i, v i (bundle σ i) < b i;
  ∀ (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ),
    (∀ i, IsAdditive (v i)) → IsBudgets b →
    (∀ σ, ¬ Proportional v b σ) →
    (∀ σ, Efficient v σ → ¬ AntiProportional v b σ) →
    ∀ i k : Fin 2, i ≠ k →
      (∃ σ, IsAugMinimizer v b i σ ∧ IsTruncMaximizer v b k σ) ∧
      (∀ σ τ, IsAugMinimizer v b i σ → IsTruncMaximizer v b k τ →
        ∀ j, v j (bundle σ j) = v j (bundle τ j)) := by sorry

end GenericBudgetAudit.IdenticalPrefs
