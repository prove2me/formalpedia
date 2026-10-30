-- Prove2me | Theorems.Thm_GenericBudgetAudit_IdenticalPrefs_proposition_5_1_full
-- name    : GenericBudgetAudit.IdenticalPrefs.proposition_5_1_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:31:57.022325+00:00
-- url     : https://prove2.me/theorems/deb5bfe6-08c3-435f-99a1-7e18931ccd3b
-- title:
--   Proposition 5.1 — proportional and anti-proportional allocations are supported
-- statement:
--   Let two agents have nonnegative normalized additive valuations and arbitrary positive budgets summing to one. An allocation is proportional if $v_i(S_i)\ge b_i$ for both agents; it is anti-proportional if $v_i(S_i)\le b_i$ for both and at least one inequality is strict. Both following statements hold:
--
--   $$
--   \begin{aligned}
--   &S\text{ efficient and proportional}\ \Longrightarrow\ \exists p,\ (S,p)\text{ is a CE},\\
--   &S\text{ efficient and anti-proportional}\ \Longrightarrow\ \exists p,\ (S,p)\text{ is a CE}.
--   \end{aligned}
--   $$
--
--   In each clause the same supplied allocation is supported by nonnegative common item prices, equal on jointly identical goods. This result preserves a chosen efficient allocation rather than replacing it by a different equilibrium allocation.
--
--   Differences from the source:
--   - reading: PO allocations distinguished by allocation equality, with identical-item interchangeability → efficiency and equality of frontier points use attained utility vectors; reason: pp. 6, 7, 13 and 15 allow interchangeable identical items and require strictly ordered frontier levels; two items valued 1/2 by both agents give different labelled assignments with the same efficient vector
--   - generalization: strict preferences and strict inclusion monotonicity apart from identical items → nonnegative normalized additive valuations with arbitrary ties and zero-value goods; reason: every source additive market satisfies this weaker valuation predicate; no source instance is removed and the demand domain remains all bundles
--   - encoding: finite item set M and agents 1 and 2 → items Fin m, agents Fin 2 indexed 0 and 1, allocations total item-to-agent functions; reason: finite relabelling preserves every bundle and clearing partition, including empty bundles
--   - encoding: footnote 3 on p. 6 assigns identical items the same prices in existence results → existential prices also satisfy EqualPrices for jointly identical singleton values; reason: the explicit conjunct retains the source convention for the very same equilibrium
--   - encoding: definitions shared across the paper → concrete theorem-local lets copied from the staged Model definition; reason: each draft must compile independently and cannot import another unpublished draft; the lets add no hypotheses or free predicates
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2 (2018), Proposition 5.1, p. 12. https://arxiv.org/abs/1703.08150v2

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

open scoped Classical
open GenericBudgets.AlmostEqual (bundle price IsCE)

noncomputable section

namespace GenericBudgetAudit.IdenticalPrefs

/-- Self-contained draft: concrete local lets duplicate Model, because drafts cannot import drafts. -/
theorem proposition_5_1_full {m : ℕ} :
  let IsAdditive (w : Finset (Fin m) → ℝ) : Prop :=
    (∀ j, 0 ≤ w {j}) ∧ (∀ S, w S = ∑ j ∈ S, w {j}) ∧ w Finset.univ = 1;
  let IsBudgets (b : Fin 2 → ℝ) : Prop :=
    (∀ i, 0 < b i) ∧ b 0 + b 1 = 1;
  let Efficient (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2) : Prop :=
    ∀ τ : Fin m → Fin 2, (∀ i, v i (bundle σ i) ≤ v i (bundle τ i)) →
      ∀ i, v i (bundle τ i) = v i (bundle σ i);
  let Proportional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) : Prop :=
    ∀ i, b i ≤ v i (bundle σ i);
  let AntiProportional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) : Prop :=
    (∀ i, v i (bundle σ i) ≤ b i) ∧ ∃ i, v i (bundle σ i) < b i;
  let EqualPrices (v : Fin 2 → Finset (Fin m) → ℝ) (p : Fin m → ℝ) : Prop :=
    ∀ j k, (∀ i, v i {j} = v i {k}) → p j = p k;
  ∀ (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ),
    (∀ i, IsAdditive (v i)) → IsBudgets b →
    (∀ σ, Efficient v σ → Proportional v b σ →
      ∃ p : Fin m → ℝ, IsCE v b σ p ∧ EqualPrices v p) ∧
    (∀ σ, Efficient v σ → AntiProportional v b σ →
      ∃ p : Fin m → ℝ, IsCE v b σ p ∧ EqualPrices v p) := by sorry

end GenericBudgetAudit.IdenticalPrefs
