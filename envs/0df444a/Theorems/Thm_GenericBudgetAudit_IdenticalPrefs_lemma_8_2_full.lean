-- Prove2me | Theorems.Thm_GenericBudgetAudit_IdenticalPrefs_lemma_8_2_full
-- name    : GenericBudgetAudit.IdenticalPrefs.lemma_8_2_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:33:11.177147+00:00
-- url     : https://prove2.me/theorems/54ec593d-6b77-43ff-be72-3a53b058f9bb
-- title:
--   Lemma 8.2 — all allocations efficient implies generic equilibrium existence
-- statement:
--   Let two agents have nonnegative normalized additive valuations and budgets $b_1>b_2>0$ with sum one. Let $R_i$ be the exceptional budgets determined by consecutive distinct efficient levels as in Definition 6.2. Suppose that $b\notin R_i$ for some agent $i$ and every allocation is efficient. Then a competitive equilibrium exists. The same equilibrium satisfies the conditional fairness guarantee
--
--   $$
--   \exists S,p:\quad (S,p)\text{ is a CE}\quad\text{and}\quad
--   \left[\text{no efficient anti-proportional allocation}\ \Longrightarrow\
--   v_j(S_j)\ge b_j^-\ (j=1,2)\right].
--   $$
--
--   Its prices are nonnegative and equal for jointly identical goods. Neither common preferences nor absence of anti-proportional allocations is required for the unconditional existence assertion. This lemma applies to the wider domain where all attained utility vectors are efficient.
--
--   Differences from the source:
--   - reading: PO allocations distinguished by allocation equality, with identical-item interchangeability → efficiency and equality of frontier points use attained utility vectors; reason: pp. 6, 7, 13 and 15 allow interchangeable identical items and require strictly ordered frontier levels; two items valued 1/2 by both agents give different labelled assignments with the same efficient vector
--   - generalization: strict preferences and strict inclusion monotonicity apart from identical items → nonnegative normalized additive valuations with arbitrary ties and zero-value goods; reason: every source additive market satisfies this weaker valuation predicate; no source instance is removed and the demand domain remains all bundles
--   - encoding: finite item set M and agents 1 and 2 → items Fin m, agents Fin 2 indexed 0 and 1, allocations total item-to-agent functions; reason: finite relabelling preserves every bundle and clearing partition, including empty bundles
--   - encoding: truncated share is an attained maximum of a frontier slice → an Option real maximum, with GetsTruncatedShare requiring some value and its inequality; reason: none records an empty slice instead of silently using zero; the source-domain slices are nonempty in each applicable theorem
--   - encoding: budget ratio equality between consecutive PO allocations → b_i (1-x) = (1-b_i) y for consecutive distinct efficient levels x<y; reason: 0 ≤ x < y ≤ 1 makes both source denominators y and 1-x positive; using b_i swaps budget coordinates correctly for the second agent
--   - encoding: footnote 3 on p. 6 assigns identical items the same prices in existence results → existential prices also satisfy EqualPrices for jointly identical singleton values; reason: the explicit conjunct retains the source convention for the very same equilibrium
--   - encoding: definitions shared across the paper → concrete theorem-local lets copied from the staged Model definition; reason: each draft must compile independently and cannot import another unpublished draft; the lets add no hypotheses or free predicates
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2 (2018), Lemma 8.2, p. 20. https://arxiv.org/abs/1703.08150v2

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

open scoped Classical
open GenericBudgets.AlmostEqual (bundle price IsCE)

noncomputable section

namespace GenericBudgetAudit.IdenticalPrefs

/-- Self-contained draft: concrete local lets duplicate Model, because drafts cannot import drafts. -/
theorem lemma_8_2_full {m : ℕ} :
  let IsAdditive (w : Finset (Fin m) → ℝ) : Prop :=
    (∀ j, 0 ≤ w {j}) ∧ (∀ S, w S = ∑ j ∈ S, w {j}) ∧ w Finset.univ = 1;
  let IsBudgets (b : Fin 2 → ℝ) : Prop :=
    (∀ i, 0 < b i) ∧ b 0 + b 1 = 1;
  let Efficient (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2) : Prop :=
    ∀ τ : Fin m → Fin 2, (∀ i, v i (bundle σ i) ≤ v i (bundle τ i)) →
      ∀ i, v i (bundle τ i) = v i (bundle σ i);
  let frontierLevels (v : Fin 2 → Finset (Fin m) → ℝ) (i : Fin 2) : Finset ℝ :=
    (Finset.univ.filter (Efficient v)).image (fun σ => v i (bundle σ i));
  let truncatedShare (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (i : Fin 2) : Option ℝ :=
    let levels := (frontierLevels v i).filter (fun x => x ≤ b i)
    if h : levels.Nonempty then some (levels.max' h) else none;
  let GetsTruncatedShare (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) (i : Fin 2) : Prop :=
    ∃ x : ℝ, truncatedShare v b i = some x ∧ x ≤ v i (bundle σ i);
  let AntiProportional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) : Prop :=
    (∀ i, v i (bundle σ i) ≤ b i) ∧ ∃ i, v i (bundle σ i) < b i;
  let EqualPrices (v : Fin 2 → Finset (Fin m) → ℝ) (p : Fin m → ℝ) : Prop :=
    ∀ j k, (∀ i, v i {j} = v i {k}) → p j = p k;
  let InExceptional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (i : Fin 2) : Prop :=
    ∃ x ∈ frontierLevels v i, ∃ y ∈ frontierLevels v i, x < y ∧
      (∀ z ∈ frontierLevels v i, ¬ (x < z ∧ z < y)) ∧
      b i * (1 - x) = (1 - b i) * y;
  ∀ (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ),
    (∀ i, IsAdditive (v i)) → IsBudgets b → b 1 < b 0 →
    (∃ i : Fin 2, ¬ InExceptional v b i) → (∀ σ, Efficient v σ) →
    ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ),
      IsCE v b σ p ∧ EqualPrices v p ∧
      ((∀ τ, Efficient v τ → ¬ AntiProportional v b τ) →
        ∀ j, GetsTruncatedShare v b σ j) := by sorry

end GenericBudgetAudit.IdenticalPrefs
