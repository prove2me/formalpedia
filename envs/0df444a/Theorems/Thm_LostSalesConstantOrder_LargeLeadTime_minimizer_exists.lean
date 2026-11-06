-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_minimizer_exists
-- name    : LostSalesConstantOrder.LargeLeadTime.minimizer_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:45.256996+00:00
-- url     : https://prove2.me/theorems/cccc6c6f-2f5f-4fca-81d0-f7729a4fbb06
-- title:
--   Problem (4) has a solution $(\mathbf x^*,\mathcal I^*)$
-- statement:
--   In the lost-sales system with lead time $L$, costs $h,c>0$ and demand law $\mathcal D$ (finite third moment, not deterministic), let $Q$ be the $c/(c+h)$ quantile of $\mathcal D$. The optimization problem
--   $$
--   \min_{\mathbf x\in[\mathbf 0,Q\mathbf 1],\ \mathcal I\in\mathbb R^+}\ \mathbb E\Big[\sum_{t=\tau}^{\tau+L-1}C^\pi_t\ \Big|\ \mathbf x^\pi_\tau=\mathbf x,\ I^\pi_\tau=\mathcal I\Big]\tag{4}
--   $$
--   has a solution $(\mathbf x^*,\mathcal I^*)$.
--
--   This guarantees that Lemmas 6, 7, 10, Theorem 8 and Corollary 12, which are stated for any solution of (4), are not vacuous.
--
--   **Formalization Note** The conditional expectation is the expected cost of $L$ periods of the system started with pipeline $\mathbf x$ and inventory $\mathcal I$ (`windowCost`), which depends on neither $\pi$ nor $\tau$.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 8, §5, sentence after (4)

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- §5, after (4), p. 8 (unnumbered): problem (4),
`min_{x ∈ [0, Q1], 𝓘 ∈ ℝ⁺} E[Σ_{t=τ}^{τ+L−1} C_t^π | x^π_τ = x, I^π_τ = 𝓘]`, has a solution
`(x*, 𝓘*)`. -/
theorem minimizer_exists (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P) :
    ∃ (x : Fin prm.L → ℝ≥0) (I : ℝ≥0), IsWindowMinimizer P prm x I := by sorry

end LostSalesConstantOrder.LargeLeadTime
