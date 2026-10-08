-- Prove2me | Theorems.Thm_GenericBudgets_AlmostEqual_proposition_5_1
-- name    : GenericBudgets.AlmostEqual.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:21.148999+00:00
-- url     : https://prove2.me/theorems/4005304d-585b-4a11-8291-4863f5b77f01
-- title:
--   Proposition 5.1 — budget-proportional and anti-proportional PO allocations are supported in a CE
-- statement:
--   Consider two agents with additive, normalized, non-negative, monotone and strict valuations $v_1,v_2$ on $m$ indivisible items, and positive budgets with $b_1+b_2=1$. Let $\mathcal S$ be a Pareto optimal allocation.
--   1. If $\mathcal S$ is **budget-proportional**, i.e. $v_i(\mathcal S_i)\ge b_i$ for both agents, then there are prices $p$ such that $(\mathcal S,p)$ is a competitive equilibrium.
--   2. If $\mathcal S$ is **anti-proportional**, i.e. $v_i(\mathcal S_i)\le b_i$ for both agents with strict inequality for at least one, then there are prices $p$ such that $(\mathcal S,p)$ is a competitive equilibrium.
--
--   In symbols, with $\mathrm{CE}(\mathcal S)$ meaning "$\mathcal S$ is supported in a CE at budgets $b$":
--   $$\mathcal S\ \text{PO and budget-proportional (or anti-proportional)}\ \Longrightarrow\ \exists p,\ (\mathcal S,p)\text{ is a CE}.$$
--
--   This settles CE existence whenever a budget-proportional allocation exists (Theorem 5.2) and is the first case of Theorem 7.1's proof.
--
--   **Formalization Note** The page says "any budgets"; its proof normalizes them, and the statement carries $b_1+b_2=1$, the paper's standing convention. Proportional shares are written $b_i\,v_i(M)$, equal to $b_i$ under normalization. Strictness is taken as plain injectivity of each valuation on bundles; the paper's single exception for identical items (p. 6) is dropped, so markets with identical items are excluded. The paper's agents 1 and 2 are the indices 0 and 1 of `Fin 2`.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 12, Proposition 5.1

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.AlmostEqual

theorem proposition_5_1 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsStandardValuation (v i))
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1)
    (σ : Fin m → Fin 2) (hPO : IsPO v σ) :
    (IsBudgetProportional v b σ → ∃ p, IsCE v b σ p) ∧
      (IsAntiProportional v b σ → ∃ p, IsCE v b σ p) := by sorry
end GenericBudgets.AlmostEqual
