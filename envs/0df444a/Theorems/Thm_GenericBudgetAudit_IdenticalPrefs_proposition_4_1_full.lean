-- Prove2me | Theorems.Thm_GenericBudgetAudit_IdenticalPrefs_proposition_4_1_full
-- name    : GenericBudgetAudit.IdenticalPrefs.proposition_4_1_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:31:08.67122+00:00
-- url     : https://prove2.me/theorems/aa8415c1-b444-4773-a25b-8c6e59fadfa6
-- title:
--   Proposition 4.1 — characterization of a budget-exhausting equilibrium
-- statement:
--   Let two agents have nonnegative, normalized, weakly monotone cardinal valuations $v_i$ on all bundles of a finite market and positive budgets $b_1+b_2=1$. Let $S$ be an efficient clearing allocation with both bundles nonempty, and let $p$ be nonnegative item prices exhausting both budgets. Write $v_i(A\mid B)=v_i(A\cup B)-v_i(B)$ and $p(A)=\sum_{j\in A}p_j$. Then
--
--   $$
--   (S,p)\text{ is a CE}\quad\Longleftrightarrow\quad
--   \forall i\ne k,\ A\subseteq S_i,\ B\subseteq S_k:\quad
--   \left[\begin{array}{l}v_i(A\mid S_i\setminus A)>v_i(B\mid S_i\setminus A),\\v_k(A\mid S_k\setminus B)>v_k(B\mid S_k\setminus B)\end{array}\right]
--   \Longrightarrow p(A)>p(B).
--   $$
--
--   Both agent orders and all subbundles are included. Efficiency means that no allocation weakly improves both utilities and strictly improves one. This characterization connects equilibrium demand to the prices of possible exchanges; it does not restrict preferences to additive ones.
--
--   Differences from the source:
--   - reading: PO allocations distinguished by allocation equality, with identical-item interchangeability → efficiency and equality of frontier points use attained utility vectors; reason: pp. 6, 7, 13 and 15 allow interchangeable identical items and require strictly ordered frontier levels; two items valued 1/2 by both agents give different labelled assignments with the same efficient vector
--   - generalization: strict inclusion monotonicity and strict preferences apart from identical items → nonnegative normalized weakly monotone cardinal valuations with arbitrary indifferences; reason: every source cardinal valuation satisfies the predicate; the characterization compares only strict improvements and ordinary Pareto domination
--   - encoding: finite item set M and agents 1 and 2 → items Fin m, agents Fin 2 indexed 0 and 1, allocations total item-to-agent functions; reason: finite relabelling preserves every bundle and clearing partition, including empty bundles
--   - encoding: definitions shared across the paper → concrete theorem-local lets copied from the staged Model definition; reason: each draft must compile independently and cannot import another unpublished draft; the lets add no hypotheses or free predicates
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2 (2018), Proposition 4.1, p. 10. https://arxiv.org/abs/1703.08150v2

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

open scoped Classical
open GenericBudgets.AlmostEqual (bundle price IsCE)

noncomputable section

namespace GenericBudgetAudit.IdenticalPrefs

/-- Self-contained draft: concrete local lets duplicate Model, because drafts cannot import drafts. -/
theorem proposition_4_1_full {m : ℕ} :
  let IsCardinal (w : Finset (Fin m) → ℝ) : Prop :=
    (∀ S, 0 ≤ w S) ∧ w Finset.univ = 1 ∧ ∀ S T, S ⊆ T → w S ≤ w T;
  let IsBudgets (b : Fin 2 → ℝ) : Prop :=
    (∀ i, 0 < b i) ∧ b 0 + b 1 = 1;
  let Efficient (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2) : Prop :=
    ∀ τ : Fin m → Fin 2, (∀ i, v i (bundle σ i) ≤ v i (bundle τ i)) →
      ∀ i, v i (bundle τ i) = v i (bundle σ i);
  let Exhausting (b : Fin 2 → ℝ) (σ : Fin m → Fin 2) (p : Fin m → ℝ) : Prop :=
    ∀ i, price p (bundle σ i) = b i;
  let marginal (w : Finset (Fin m) → ℝ) (A B : Finset (Fin m)) : ℝ :=
    w (A ∪ B) - w B;
  let SwapCondition (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2)
      (p : Fin m → ℝ) : Prop :=
    ∀ i k : Fin 2, i ≠ k → ∀ A B : Finset (Fin m),
      A ⊆ bundle σ i → B ⊆ bundle σ k →
      marginal (v i) B (bundle σ i \ A) < marginal (v i) A (bundle σ i \ A) →
      marginal (v k) B (bundle σ k \ B) < marginal (v k) A (bundle σ k \ B) →
      price p B < price p A;
  ∀ (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (σ : Fin m → Fin 2) (p : Fin m → ℝ),
    (∀ i, IsCardinal (v i)) → IsBudgets b → Efficient v σ →
    (∀ i, (bundle σ i).Nonempty) → (∀ j, 0 ≤ p j) → Exhausting b σ p →
    (IsCE v b σ p ↔ SwapCondition v σ p) := by sorry

end GenericBudgetAudit.IdenticalPrefs
