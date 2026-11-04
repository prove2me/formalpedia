-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_4
-- name    : LostSalesConstantOrder.LargeLeadTime.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:25.913271+00:00
-- url     : https://prove2.me/theorems/3af0565b-f3a0-41ca-9043-74481c9a788d
-- title:
--   Lemma 4: the cost of $\pi_r$ over L consecutive periods
-- statement:
--   In the lost-sales system with demand law $\mathcal D$ (finite third moment, not deterministic), let $r\in[0,\mathbb E[D])$ and let $\pi_r$ be the constant-order policy that orders $I^r_\infty+r$ in the first period and $r$ afterwards. Let $I^r_{1,\infty}$ be a copy of $I^r_\infty$ independent of the demands $D_1,D_2,\dots$, and let $i^r_k$ be the largest index attaining $W^r_k=\max_{j=0,\dots,k}(jr-\sum_{i=1}^jD_i+\delta_{j,k}I^r_{1,\infty})$. Then for every $\tau\ge L+1$,
--   $$
--   \mathbb E\Big[\sum_{t=\tau}^{\tau+L-1}C^{\pi_r}_t\Big]=h\sum_{k=1}^L\mathbb E\Big[i^r_kr-\sum_{i=1}^{i^r_k}D_i+\delta_{i^r_k,k}I^r_{1,\infty}\Big]+c\big(L\,\mathbb E[D]-Lr\big).
--   $$
--
--   It specializes Lemma 3 to the constant-order policy, whose inventory levels are stationary from period $L+1$ on.
--
--   **Formalization Note** The window starts at Lean period $t_0\ge L$ (the paper's $\tau=t_0+1\in[L+1,T+1]$ for all $T$). The expectation is over the product of the law of $I^r_\infty$ and the i.i.d. demand law. The right-hand side is a nonnegative real mapped into $[0,\infty]$.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 7, Lemma 4

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_ConstantOrder

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Lemma 4, p. 7: for `r ∈ [0, E[D])` and every window start `t₀ ≥ L` (the paper's
`τ = t₀ + 1 ∈ [L + 1, T + 1]`), the expected cost of `π_r` over the `L` periods `t₀, …, t₀ + L − 1` is
`h Σ_{k=1}^L E[i^r_k r − Σ_{i=1}^{i^r_k} D_i + δ_{i^r_k,k} I^r_{1,∞}] + c(L E[D] − L r)`, the
expectation taken over an independent pair `(I^r_{1,∞}, (D_i))`. -/
theorem lemma_4 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (r : ℝ≥0) (hr : (r : ℝ) < CappedBaseStock.mean P) (t₀ : ℕ) (ht₀ : prm.L ≤ t₀) :
    costWindow P prm (constantOrderPolicy P r) t₀ =
      ENNReal.ofReal
        (prm.h * ∑ k ∈ Finset.Icc 1 prm.L,
            ∫ p, ((ik r k p.1 p.2 : ℝ) * r -
                ∑ i ∈ Finset.Icc 1 (ik r k p.1 p.2), (p.2 (i - 1) : ℝ) +
                if ik r k p.1 p.2 = k then (p.1 : ℝ) else 0)
              ∂((lawSupWalk P r).prod (CappedBaseStock.demandPathLaw P)) +
          prm.p * (prm.L * CappedBaseStock.mean P - prm.L * r)) := by sorry

end LostSalesConstantOrder.LargeLeadTime
