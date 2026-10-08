-- Prove2me | Theorems.Thm_GenericBudgets_IdenticalPrefs_lemma_6_3
-- name    : GenericBudgets.IdenticalPrefs.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:04.105113+00:00
-- url     : https://prove2.me/theorems/689ee0a7-be29-40e9-ab3b-9c216fd73a31
-- title:
--   Lemma 6.3 — main technical tool: budgets outside R_i and an empty rectangle T_i give a CE with truncated shares
-- statement:
--   Consider two agents with standard (additive, normalized, non-negative, monotone, strict) valuations $v_1, v_2$ and budgets $b_1 > b_2 > 0$ with $b_1 + b_2 = 1$. Assume that
--
--   1. no allocation is budget-proportional, and no Pareto optimal allocation is anti-proportional;
--   2. for some agent $i$, with $k$ the other agent, the budget pair is outside the zero-measure set $R_i(v_1,v_2)$ of Definition 6.2, and the rectangle $T_i = T_i(b_i, v_1, v_2)$ of Definition 6.1 contains no allocation.
--
--   Then there is a competitive equilibrium $(\mathcal S, p)$ in which every agent $j$ gets her truncated share:
--   $$v_j(\mathcal S_j) \ge b_j^- \qquad (j = 1, 2).$$
--
--   This lemma is the engine of the paper's existence results: both Theorem 7.1 (almost equal budgets) and Theorem 8.1 (identical preferences) reduce to verifying its two conditions.
--
--   **Formalization Note** Agents are indexed $0, 1$ for the paper's $1, 2$, so $b_1 > b_2$ is `b 1 < b 0`. The agents $i \ne k$ are passed explicitly. "$T_i$ is empty" is `∀ σ, ¬ InRectT v b i k σ`; `InRectT` quantifies over the maximizing PO allocations $\hat{\mathcal S}^i, \hat{\mathcal S}^k$, which exist and are unique under the standing assumptions. Valuations are strict without the identical-items exception. The statement is identical, up to its namespace, to the Lemma 6.3 milestone of mission 1 of this series.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 15, Lemma 6.3

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.IdenticalPrefs

theorem lemma_6_3 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, GenericBudgets.AlmostEqual.IsStandardValuation (v i))
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1) (hlt : b 1 < b 0)
    (hnoBP : ∀ σ, ¬ GenericBudgets.AlmostEqual.IsBudgetProportional v b σ)
    (hnoAP : ∀ σ, GenericBudgets.AlmostEqual.IsPO v σ → ¬ GenericBudgets.AlmostEqual.IsAntiProportional v b σ)
    (i k : Fin 2) (hik : i ≠ k) (hR : ¬ GenericBudgets.AlmostEqual.InR v b i) (hT : ∀ σ, ¬ GenericBudgets.AlmostEqual.InRectT v b i k σ) :
    ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ), GenericBudgets.AlmostEqual.IsCE v b σ p ∧ ∀ j, GenericBudgets.AlmostEqual.GetsTruncatedShare v b σ j := by sorry

end GenericBudgets.IdenticalPrefs
