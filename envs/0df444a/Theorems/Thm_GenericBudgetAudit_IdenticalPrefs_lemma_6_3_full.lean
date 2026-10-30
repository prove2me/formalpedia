-- Prove2me | Theorems.Thm_GenericBudgetAudit_IdenticalPrefs_lemma_6_3_full
-- name    : GenericBudgetAudit.IdenticalPrefs.lemma_6_3_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:32:47.224318+00:00
-- url     : https://prove2.me/theorems/7f077158-8472-4fc9-888b-38b7a9900add
-- title:
--   Lemma 6.3 — genericity and an empty rectangle give a fair equilibrium
-- statement:
--   Let two agents have nonnegative normalized additive valuations, budgets $b_1>b_2>0$ with sum one, no proportional allocation, and no efficient anti-proportional allocation. For a frontier point maximizing agent $j$'s utility at or below $b_j$, write $\hat S^j$. For distinct agents $i,k$, the open rectangle $T_i$ contains every allocation $S$ satisfying
--
--   $$
--   v_i(\hat S_i^i)<v_i(S_i)<v_i(\hat S_i^k),\qquad
--   0<v_k(S_k)<v_k(\hat S_k^k).
--   $$
--
--   Let $R_i$ contain exactly the budgets satisfying $b_i(1-x)=(1-b_i)y$ for two consecutive distinct efficient utility levels $x<y$ of agent $i$. If there is some agent $i$ such that $b\notin R_i$ and that same $T_i$ is empty, then
--
--   $$
--   \exists S,p:\quad (S,p)\text{ is a CE}\quad\text{and}\quad
--   v_j(S_j)\ge b_j^-\quad (j=1,2).
--   $$
--
--   The prices are nonnegative, common to both agents, and equal for jointly identical goods. The rectangle ranges over all allocations, including dominated ones. This is a sufficient equilibrium criterion on the full two-valuation domain.
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
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2 (2018), Lemma 6.3, p. 15. https://arxiv.org/abs/1703.08150v2

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

open scoped Classical
open GenericBudgets.AlmostEqual (bundle price IsCE)

noncomputable section

namespace GenericBudgetAudit.IdenticalPrefs

/-- Self-contained draft: concrete local lets duplicate Model, because drafts cannot import drafts. -/
theorem lemma_6_3_full {m : ℕ} :
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
  let IsTruncMaximizer (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (i : Fin 2) (σ : Fin m → Fin 2) : Prop :=
    Efficient v σ ∧ v i (bundle σ i) ≤ b i ∧
      ∀ τ, Efficient v τ → v i (bundle τ i) ≤ b i → v i (bundle τ i) ≤ v i (bundle σ i);
  let GetsTruncatedShare (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) (i : Fin 2) : Prop :=
    ∃ x : ℝ, truncatedShare v b i = some x ∧ x ≤ v i (bundle σ i);
  let Proportional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) : Prop :=
    ∀ i, b i ≤ v i (bundle σ i);
  let AntiProportional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) : Prop :=
    (∀ i, v i (bundle σ i) ≤ b i) ∧ ∃ i, v i (bundle σ i) < b i;
  let EqualPrices (v : Fin 2 → Finset (Fin m) → ℝ) (p : Fin m → ℝ) : Prop :=
    ∀ j k, (∀ i, v i {j} = v i {k}) → p j = p k;
  let InRectangle (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (i k : Fin 2) (σ : Fin m → Fin 2) : Prop :=
    ∃ σi σk, IsTruncMaximizer v b i σi ∧ IsTruncMaximizer v b k σk ∧
      v i (bundle σi i) < v i (bundle σ i) ∧
      v i (bundle σ i) < v i (bundle σk i) ∧
      0 < v k (bundle σ k) ∧ v k (bundle σ k) < v k (bundle σk k);
  let InExceptional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (i : Fin 2) : Prop :=
    ∃ x ∈ frontierLevels v i, ∃ y ∈ frontierLevels v i, x < y ∧
      (∀ z ∈ frontierLevels v i, ¬ (x < z ∧ z < y)) ∧
      b i * (1 - x) = (1 - b i) * y;
  ∀ (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ),
    (∀ i, IsAdditive (v i)) → IsBudgets b → b 1 < b 0 →
    (∀ σ, ¬ Proportional v b σ) →
    (∀ σ, Efficient v σ → ¬ AntiProportional v b σ) →
    (∃ i k : Fin 2, i ≠ k ∧ ¬ InExceptional v b i ∧
      ∀ σ, ¬ InRectangle v b i k σ) →
    ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ),
      IsCE v b σ p ∧ EqualPrices v p ∧ ∀ j, GetsTruncatedShare v b σ j := by sorry

end GenericBudgetAudit.IdenticalPrefs
