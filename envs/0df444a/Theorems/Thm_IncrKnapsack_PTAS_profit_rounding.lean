-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_profit_rounding
-- name    : IncrKnapsack.PTAS.profit_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:17.136184+00:00
-- url     : https://prove2.me/theorems/1428a501-ac07-44e9-87f7-20e84fa6843c
-- title:
--   §2.2, p. 8 — rounding profits down to powers of 1 + ε loses at most an ε-fraction of Ψ
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, and let $\epsilon = 1/K$ with $K > 4$ an integer. Scale all profits by $1/p_{\min}$, where $p_{\min} = \min_i p_i$, and round each scaled profit down to the nearest integer power of $1 + \epsilon$. Call the result $\hat p_i = (1+\epsilon)^{\ell(i)}$. Then for every solution $\mathcal S$:
--
--   $$p_{\min} \cdot \Psi_{\hat p}(\mathcal S) \;\le\; \Psi_p(\mathcal S) \qquad\text{and}\qquad (1-\epsilon)\cdot\Psi_p(\mathcal S) \;\le\; p_{\min}\cdot\Psi_{\hat p}(\mathcal S).$$
--
--   Here $\Psi_p$ and $\Psi_{\hat p}$ are the objectives under the original and the rounded profits. The first inequality says that restoring the original profits can only increase the profit of a solution. The second says that the rounding loses at most an $\epsilon$-fraction of it. Together they transfer an approximation guarantee for the rounded instance back to the original one, at the cost of a factor $1-\epsilon$.
--
--   **Formalization Note.** The page states the loss for the optimal solution $\mathcal S^*$; the statement here holds for every solution. The rounded profits keep the scaling by $1/p_{\min}$, which is why $p_{\min}$ appears on both sides.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, p. 8, §2.2, 'Profit classes'

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem profit_rounding (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K)
    (S : Sol I) :
    pmin I * Psi I (pr I K) S ≤ Psi I I.p S ∧
      (1 - eps K) * Psi I I.p S ≤ pmin I * Psi I (pr I K) S := by sorry
end IncrKnapsack.PTAS
