-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_6
-- name    : LostSalesConstantOrder.LargeLeadTime.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:17.865047+00:00
-- url     : https://prove2.me/theorems/5edbff1a-c286-4868-86e2-cff83cfcc5d8
-- title:
--   Lemma 6: lower bound on the cost of $\bar\pi$ over L periods through $V_k$
-- statement:
--   In the lost-sales system with demand law $\mathcal D$ (finite third moment, not deterministic), let $\pi$ be an admissible policy that with probability one never orders more than $Q$ (such as the optimal policy $\bar\pi$ of Lemma 5), and let $(\mathbf x^*,\mathcal I^*)$ be any solution of problem (4). With $V_k=\max_{j=0,\dots,k}(\sum_{i=k+1-j}^kx^*_i-\sum_{i=1}^jD_i+\delta_{j,k}\mathcal I^*)$ and $I^*_{L+1}$ the inventory at the end of $L$ periods started from $(\mathbf x^*,\mathcal I^*)$, for every period $\tau$,
--   $$
--   \mathbb E\Big[\sum_{t=\tau}^{\tau+L-1}C^{\pi}_t\Big]\ \ge\ h\sum_{k=1}^L\mathbb E[V_k]+c\Big(\mathbb E[I^*_{L+1}]-\mathcal I^*+L\,\mathbb E[D]-\sum_{i=1}^Lx^*_i\Big).
--   $$
--
--   The right-hand side is the cost of the most favourable state allowed by Lemma 5; it is the lower bound that the constant-order policy is compared with.
--
--   **Formalization Note** The paper states this for the optimal policy $\bar\pi$ of Lemma 5; its proof uses only that $\bar\pi$ never orders more than $Q$, so the statement is made for every such policy, a class containing $\bar\pi$. The window starts at Lean period $t_0$ (the paper's $\tau=t_0+1$), for every $t_0$. The real right-hand side is mapped into $[0,\infty]$ with `ENNReal.ofReal`, which is equivalent to the real inequality because the left side is nonnegative.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 8, Lemma 6 and the definition of V_k

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_RandomWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Lemma 6, p. 8. `π` is any admissible policy that a.s. never orders more than `Q` (Lemma 5's
optimal policy `π̄` is one), `(x*, 𝓘*)` any solution of (4), and `t₀` any window start (the paper's
`τ = t₀ + 1`). Then
`E[Σ_{t=τ}^{τ+L−1} C_t^π] ≥ h Σ_{k=1}^L E[V_k] + c(E[I*_{L+1}] − 𝓘* + L E[D] − Σ_{i=1}^L x*_i)`. -/
theorem lemma_6 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (π : CappedBaseStock.AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I) (t₀ : ℕ) :
    ENNReal.ofReal
        (prm.h * ∑ k ∈ Finset.Icc 1 prm.L, ∫ d, Vk x I k d ∂CappedBaseStock.demandPathLaw P +
          prm.p * ((∫ d, (endInventory prm x I d : ℝ) ∂CappedBaseStock.demandPathLaw P) -
            I + prm.L * CappedBaseStock.mean P - ∑ i, (x i : ℝ))) ≤
      costWindow P prm π t₀ := by sorry

end LostSalesConstantOrder.LargeLeadTime
