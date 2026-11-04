-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_theorem_8
-- name    : LostSalesConstantOrder.LargeLeadTime.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:14.017863+00:00
-- url     : https://prove2.me/theorems/c6357084-e3bf-4064-85c0-5571f6881495
-- title:
--   Theorem 8: $\pi_{r^*}$ is within $h(Q+2^{3/2}\mathbb E[D])\Theta_{r^*}^{-3}+c\mathcal I^*$ of $\bar\pi$ over L periods
-- statement:
--   In the lost-sales system with demand law $\mathcal D$ (finite third moment, not deterministic), let $\pi$ be an admissible policy that never orders more than $Q$ (such as $\bar\pi$ of Lemma 5), let $(\mathbf x^*,\mathcal I^*)$ solve problem (4), and let $r^*=L^{-1}\sum_{i=1}^Lx^*_i$. If $r^*<\mathbb E[D]$, then for every $\tau\ge L+1$,
--   $$
--   \mathbb E\Big[\sum_{t=\tau}^{\tau+L-1}C^{\pi_{r^*}}_t\Big]-\mathbb E\Big[\sum_{t=\tau}^{\tau+L-1}C^{\pi}_t\Big]\ \le\ h\big(Q+2^{3/2}\mathbb E[D]\big)\Theta_{r^*}^{-3}+c\mathcal I^*.\tag{7}
--   $$
--
--   It bounds the per-window gap between the constant-order policy that mimics the most favourable pipeline and an optimal policy by a quantity that does not grow with $L$ once $r^*$ stays away from $\mathbb E[D]$.
--
--   **Formalization Note** The difference (7) is stated additively, $\mathbb E[\cdot^{\pi_{r^*}}]\le\mathbb E[\cdot^{\pi}]+(\text{bound})$ in $[0,\infty]$, which is the paper's inequality whenever the second expectation is finite (it is, for a policy with bounded orders). The paper states the result for $\bar\pi$; its proof uses only that $\bar\pi$ never orders more than $Q$. The window starts at Lean period $t_0\ge L$, the paper's $\tau\in[L+1,T+1]$ for all $T$. $2^{3/2}$ is written $2\sqrt2$.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, pp. 9–10, Theorem 8 and (7)

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_ConstantOrder

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Theorem 8, pp. 9–10. `π` is any admissible policy that a.s. never orders more than `Q`
(Lemma 5's `π̄` is one) and `(x*, 𝓘*)` any solution of (4), with `r* = L⁻¹ Σ x*_i < E[D]`. For every
window start `t₀ ≥ L` (the paper's `τ ∈ [L + 1, T + 1]`), the difference (7)
`E[Σ_{t=τ}^{τ+L−1} C_t^{π_{r*}}] − E[Σ_{t=τ}^{τ+L−1} C_t^π]` is at most
`h(Q + 2^{3/2}E[D])Θ_{r*}⁻³ + c𝓘*` (stated additively; `2^{3/2} = 2√2`). -/
theorem theorem_8 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (π : CappedBaseStock.AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I)
    (hr : (rStar x : ℝ) < CappedBaseStock.mean P) (t₀ : ℕ) (ht₀ : prm.L ≤ t₀) :
    costWindow P prm (constantOrderPolicy P (rStar x)) t₀ ≤
      costWindow P prm π t₀ +
        ENNReal.ofReal
          (prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * CappedBaseStock.mean P) /
              theta P (rStar x) ^ 3 + prm.p * I) := by sorry

end LostSalesConstantOrder.LargeLeadTime
