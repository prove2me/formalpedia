-- Prove2me | Theorems.Thm_GenericBudgets_AlmostEqual_theorem_7_1
-- name    : GenericBudgets.AlmostEqual.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:29.263415+00:00
-- url     : https://prove2.me/theorems/f50bfd1a-2a84-41ab-bb53-795c3c662b22
-- title:
--   Theorem 7.1 — two additive agents with almost equal, unequal budgets have a CE giving each agent her truncated share
-- statement:
--   Consider two agents with additive, normalized, non-negative, monotone and strict valuations $v_1,v_2$ on $m$ indivisible items. There is $\epsilon>0$, depending only on $v_1,v_2$, such that for all budgets $b_1,b_2>0$ with $b_1+b_2=1$ and
--   $$b_2<b_1\le b_2+\epsilon$$
--   there exist an allocation $\mathcal S$ and item prices $p$ such that $(\mathcal S,p)$ is a competitive equilibrium and every agent gets her truncated share:
--   $$v_j(\mathcal S_j)\ \ge\ b_j^-=\max\{v_j(\mathcal S'_j):\mathcal S'\text{ PO},\ v_j(\mathcal S'_j)\le b_j\}\qquad(j=1,2).$$
--
--   With exactly equal budgets a competitive equilibrium can fail to exist already for one item. The theorem shows that this failure is a knife edge: an arbitrarily small, but strict, inequality of the budgets restores existence, together with a fairness guarantee. It is the formal version of the paper's Theorem 1.1.
--
--   **Formalization Note** "For sufficiently small $\epsilon>0$" is encoded as the existence of one $\epsilon>0$ chosen after the valuations and before the budgets; this is equivalent because the hypothesis $b_1-b_2\le\epsilon$ is monotone in $\epsilon$. "$b_1>b_2$" is `b 1 < b 0`, because the paper's agents 1, 2 are indices 0, 1. The truncated share is a maximum over Pareto optimal allocations only. Budgets are normalized as the paper assumes throughout. Strictness is taken as plain injectivity of each valuation on bundles; the paper's single exception for identical items (p. 6) is dropped, so markets with identical items are excluded.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 17, Theorem 7.1

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.AlmostEqual

theorem theorem_7_1 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsStandardValuation (v i)) :
    ∃ ε > 0, ∀ b : Fin 2 → ℝ, (∀ i, 0 < b i) → b 0 + b 1 = 1 → b 1 < b 0 → b 0 - b 1 ≤ ε →
      ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ), IsCE v b σ p ∧ ∀ i, GetsTruncatedShare v b σ i := by sorry
end GenericBudgets.AlmostEqual
