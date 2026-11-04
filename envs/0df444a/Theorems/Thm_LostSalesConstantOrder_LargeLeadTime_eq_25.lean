-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_eq_25
-- name    : LostSalesConstantOrder.LargeLeadTime.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:49.103315+00:00
-- url     : https://prove2.me/theorems/69d5883b-cf37-40a9-9286-62942798e002
-- title:
--   (25): $\mathbb E[C^{\pi_r}_t]=h\mathbb E[I^r_\infty]+c(\mathbb E[D]-r)$ for $t\ge L+1$
-- statement:
--   In the lost-sales system with demand law $\mathcal D$ (finite third moment, not deterministic), let $r\in[0,\mathbb E[D])$ and let $\pi_r$ be the constant-order policy. For every period $t\ge L+1$,
--   $$
--   \mathbb E[C^{\pi_r}_t]=h\,\mathbb E[I^r_\infty]+c\big(\mathbb E[D]-r\big).\tag{25}
--   $$
--
--   The right-hand side, minimized over $r$, defines the best constant $z$; (25) is how the guarantee proved for $\pi_{r^*}$ transfers to $\pi_z$ in the proof of Theorem 1.
--
--   **Formalization Note** Lean period $t\ge L$ is the paper's period $t+1\ge L+1$. $\mathbb E[I^r_\infty]$ is the lower integral of the supremum in $[0,\infty]$.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 15, §7.2, display (25) in the proof of Theorem 1

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_ConstantOrder

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- (25), §7.2, p. 15: for `r ∈ [0, E[D])` and every Lean period `t ≥ L` (the paper's
`t ≥ L + 1`), `E[C_t^{π_r}] = h E[I^r_∞] + c(E[D] − r)`. -/
theorem eq_25 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (r : ℝ≥0) (hr : (r : ℝ) < CappedBaseStock.mean P) (t : ℕ) (ht : prm.L ≤ t) :
    periodExpectedCost P prm (constantOrderPolicy P r) t =
      ENNReal.ofReal prm.h * ∫⁻ d, supWalk r d ∂CappedBaseStock.demandPathLaw P +
        ENNReal.ofReal (prm.p * (CappedBaseStock.mean P - r)) := by sorry

end LostSalesConstantOrder.LargeLeadTime
