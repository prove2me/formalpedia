-- Prove2me | Theorems.Thm_LeviPalRoundyShmoys2007_eq3_cost_decomposition_faithful
-- name    : LeviPalRoundyShmoys2007.eq3_cost_decomposition_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:28:45.823992+00:00
-- url     : https://prove2.me/theorems/c3b013cf-5879-4690-9956-f1b69bec8443
-- title:
--   Eq. (3): traditional cost = policy-independent terms + marginal cost
-- statement:
--   Consider the periodic-review inventory model with horizon $T$, lead time $L \le T$, ordering costs $c_t = 0$, holding costs $h_t \ge 0$, backlogging penalties $p_t \ge 0$, initial net inventory $ni_0$ and pipeline orders $q_{1-L},\dots,q_0 \ge 0$. Fix a demand path $d_1,\dots,d_T$ and nonnegative orders $Q_1,\dots,Q_T$ (with $Q_t = q_t$ for $t \le 0$). Let $NI_t$ be the net inventory at the end of period $t$, $H_t$ the marginal holding cost of Eq. (1), $\Pi_t = p_{t+L}(D_{[t,t+L]} - Y_t)^+$ the marginal backlogging cost of Eq. (2), and $H_{(-\infty,0]}$ the holding cost incurred by the units ordered before period 1 (initial stock and pipeline, consumed first-in first-out). Then
--
--   $$\sum_{t=1}^{T}\bigl(h_t\, NI_t^+ + p_t\, NI_t^-\bigr) \;=\; \sum_{t=1-L}^{0}\Pi_t \;+\; H_{(-\infty,0]} \;+\; \sum_{t=1}^{T-L}(H_t + \Pi_t).$$
--
--   This is Eq. (3) of Levi, Pál, Roundy and Shmoys (2007), combined with the convention of p. 292 that orders placed after period $T-L$ incur no cost within the horizon. The first two terms on the right do not depend on the policy, so the cost $\mathcal C(P) = \sum_{t=1}^{T-L}(H_t + \Pi_t)$ of Eq. (4), which the two-approximation theorem bounds, differs from the true period-by-period cost by a policy-independent nonnegative amount.
--
--   **Formalization Note** The identity is stated pathwise, for one demand realization. Orders placed in periods $T-L+1,\dots,T$ never arrive within the horizon and do not enter either side. The hypothesis $L \le T$ ensures that the pipeline backlogging terms refer to periods inside the horizon.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), doi:10.1287/moor.1060.0205, §3.2, p. 291, Eq. (3) and p. 292, Eq. (4)

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
open LeviBalancing.DualBalancing

theorem LeviPalRoundyShmoys2007.eq3_cost_decomposition_faithful (I : Instance) (d Q : ℤ → ℝ)
    (hL : I.L ≤ I.T) (hQ : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ Q t) :
    ∑ t ∈ Finset.Icc (1 : ℤ) (I.T : ℤ), periodCost I d Q t =
      ∑ t ∈ Finset.Icc (1 - (I.L : ℤ)) 0, marginalBacklog I d Q t + initialHolding I d +
        marginalCost I d Q := by sorry
