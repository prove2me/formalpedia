-- Prove2me | Theorems.Thm_GenericBudgets_AlmostEqual_lemma_6_3
-- name    : GenericBudgets.AlmostEqual.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:44.751179+00:00
-- url     : https://prove2.me/theorems/c6033395-4ce1-447c-895f-b03252c94674
-- title:
--   Lemma 6.3 — main technical tool: outside $R_i$ and with $T_i$ empty, a CE with truncated shares exists
-- statement:
--   Consider two agents with additive, normalized, non-negative, monotone and strict valuations $v_1,v_2$ on $m$ indivisible items, and budgets $b_1>b_2>0$ with $b_1+b_2=1$. Assume that no allocation is budget-proportional and no Pareto optimal allocation is anti-proportional. Let $i\ne k$ be the two agents and suppose
--   1. the budget pair is generic for agent $i$: $(b_1,b_2)\notin R_i(v_1,v_2)$ (Definition 6.2), and
--   2. the rectangle $T_i=T_i(b_i,v_1,v_2)$ of Definition 6.1 contains no allocation.
--
--   Then there exist an allocation $\mathcal S$ and prices $p$ such that $(\mathcal S,p)$ is a competitive equilibrium and
--   $$v_j(\mathcal S_j)\ge b_j^-\qquad\text{for both agents } j,$$
--   i.e. every agent gets her truncated share.
--
--   This is the engine of both generic existence results of the paper (Theorem 7.1 for almost equal budgets and Theorem 8.1 for identical preferences).
--
--   **Formalization Note** The two agents are passed as indices `i k` of `Fin 2` with `i ≠ k`; "$(b_1,b_2)\notin R_i$" is `¬ InR v b i`, and "$T_i$ is empty" is that no allocation satisfies `InRectT v b i k`. "$b_1>b_2$" is `b 1 < b 0`, because the paper's agents 1, 2 are indices 0, 1. Budgets are normalized as the paper assumes throughout. Strictness is taken as plain injectivity of each valuation on bundles; the paper's single exception for identical items (p. 6) is dropped, so markets with identical items are excluded.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 15, Lemma 6.3

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.AlmostEqual

theorem lemma_6_3 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsStandardValuation (v i))
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1) (hlt : b 1 < b 0)
    (hnoBP : ∀ σ, ¬ IsBudgetProportional v b σ)
    (hnoAP : ∀ σ, IsPO v σ → ¬ IsAntiProportional v b σ)
    (i k : Fin 2) (hik : i ≠ k) (hR : ¬ InR v b i) (hT : ∀ σ, ¬ InRectT v b i k σ) :
    ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ), IsCE v b σ p ∧ ∀ j, GetsTruncatedShare v b σ j := by sorry

end GenericBudgets.AlmostEqual
