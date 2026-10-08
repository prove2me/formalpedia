-- Prove2me | Theorems.Thm_GenericBudgets_AlmostEqual_lemma_4_3
-- name    : GenericBudgets.AlmostEqual.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:27.287517+00:00
-- url     : https://prove2.me/theorems/7633159f-4929-4f2c-8f69-6785995d0e4d
-- title:
--   Lemma 4.3 — a budget-exhausting combination pricing supports a PO allocation as a CE
-- statement:
--   Consider two agents with additive, normalized, non-negative, monotone and strict valuations $v_1,v_2$ on bundles of $m$ indivisible items, and budgets $b_1\ge b_2>0$ (possibly equal). Let $\mathcal S$ be a Pareto optimal allocation and let $p$ be a **combination pricing**,
--   $$p_j=\alpha\,v_1(\{j\})+\beta\,v_2(\{j\}),\qquad \alpha,\beta\ge 0,\ \max\{\alpha,\beta\}>0,$$
--   that is budget-exhausting for $\mathcal S$, i.e. $p(\mathcal S_1)=b_1$ and $p(\mathcal S_2)=b_2$. Then $(\mathcal S,p)$ is a competitive equilibrium.
--
--   This sufficient condition is the workhorse of the paper's existence results: every CE constructed later is a combination pricing at a suitable PO allocation.
--
--   **Formalization Note** The budgets are not normalized, as on the page. Strictness is taken as plain injectivity of each valuation on bundles; the paper's single exception for identical items (p. 6) is dropped, so markets with identical items are excluded. The paper's agents 1 and 2 are the indices 0 and 1 of `Fin 2`.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 11, Lemma 4.3

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.AlmostEqual

theorem lemma_4_3 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsStandardValuation (v i))
    (b : Fin 2 → ℝ) (hb1 : 0 < b 1) (hle : b 1 ≤ b 0)
    (σ : Fin m → Fin 2) (hPO : IsPO v σ)
    (p : Fin m → ℝ) (hcomb : IsCombinationPricing v p) (hex : IsBudgetExhausting b σ p) :
    IsCE v b σ p := by sorry
end GenericBudgets.AlmostEqual
