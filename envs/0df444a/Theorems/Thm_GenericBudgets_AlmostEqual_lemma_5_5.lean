-- Prove2me | Theorems.Thm_GenericBudgets_AlmostEqual_lemma_5_5
-- name    : GenericBudgets.AlmostEqual.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:39.327313+00:00
-- url     : https://prove2.me/theorems/0a09807f-765a-4e91-a593-27b4b9a8c141
-- title:
--   Lemma 5.5 — the augmented-share minimizer of one agent is the truncated-share maximizer of the other
-- statement:
--   Consider two agents $i\ne k$ with additive, normalized, non-negative, monotone and strict valuations on $m$ indivisible items, and positive budgets with $b_i+b_k=1$. Assume that no allocation is budget-proportional and no Pareto optimal allocation is anti-proportional. Then:
--   1. agent $i$'s augmented-share minimizer $\check{\mathcal S}^i$ exists: some PO allocation minimizes $v_i(\mathcal S_i)$ among PO allocations with $v_i(\mathcal S_i)\ge b_i$;
--   2. every such minimizer is agent $k$'s truncated-share maximizer:
--   $$\check{\mathcal S}^i=\hat{\mathcal S}^k,$$
--   that is, $\check{\mathcal S}^i$ gives agent $i$ the share $b_i^+$ and agent $k$ the share $b_k^-$.
--
--   The lemma reduces the four "as fair as possible" PO allocations $\hat{\mathcal S}^1,\hat{\mathcal S}^2,\check{\mathcal S}^1,\check{\mathcal S}^2$ to two, each giving both agents at least their truncated share. These are the candidate CE allocations of Lemma 6.3.
--
--   **Formalization Note** The existence part makes explicit what the page presupposes when it speaks of "the PO allocation $\check{\mathcal S}^i$". Budgets are normalized, as the paper assumes throughout. Strictness is taken as plain injectivity of each valuation on bundles; the paper's single exception for identical items (p. 6) is dropped, so markets with identical items are excluded. The paper's agents 1 and 2 are the indices 0 and 1 of `Fin 2`.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 14, Lemma 5.5

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.AlmostEqual

theorem lemma_5_5 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsStandardValuation (v i))
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1)
    (hnoBP : ∀ σ, ¬ IsBudgetProportional v b σ)
    (hnoAP : ∀ σ, IsPO v σ → ¬ IsAntiProportional v b σ)
    (i k : Fin 2) (hik : i ≠ k) :
    (∃ σ, IsAugMinimizer v b i σ) ∧ ∀ σ, IsAugMinimizer v b i σ → IsTruncMaximizer v b k σ := by sorry
end GenericBudgets.AlmostEqual
