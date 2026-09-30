-- Prove2me | Theorems.Thm_MarkovChainChoice_SingleResource_marginal_value_monotone
-- name    : MarkovChainChoice.SingleResource.marginal_value_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:19:07.312982+00:00
-- url     : https://prove2.me/theorems/611aacd4-4f71-46e1-8f65-b385b34d31b1
-- title:
--   Marginal values of capacity decrease in capacity and increase with the time remaining
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model with the standing assumptions and $\sum_{j\in N}\lambda_j\le 1$, let $r\in\mathbb R^n$ be the product revenues and $T$ the number of periods. Write $\Delta V_t(x)=V_t(x)-V_t(x-1)$ for the value functions of the (Single Resource) dynamic program. Then
--   $$\Delta V_{t}(x)\le\Delta V_{t}(x-1)\qquad\text{for } 1\le t\le T+1,\ x\ge2,$$
--   $$\Delta V_{t+1}(x)\le\Delta V_{t}(x)\qquad\text{for } 1\le t\le T,\ x\ge1.$$
--   That is, the marginal value of capacity increases as fewer units remain and as more periods remain.
--
--   The paper attributes this to Talluri and van Ryzin (2004), for any choice model, and uses both inequalities in the proof of Theorem 5. The same result for an abstract choice model is published on Prove2Me as `RevenueManagement.choice_marginal_values`; taking its arrival probabilities equal to $1$ and its choice model equal to $P_{j,S}$ gives this statement.
--
--   **Formalization Note** The paper states the inequalities for $\Delta V_{t+1}$; the index ranges above are the ones the proof of Theorem 5 uses ($t=T+1$ is trivial since $V_{T+1}=0$). One hypothesis is added and disclosed: $\sum_j\lambda_j\le 1$, which the paper's description (at most one customer per period, arriving to purchase $j$ with probability $\lambda_j$) implies and which makes $1-\sum_jP_{j,S}$ a probability. No sign condition is placed on the revenues $r_j$, as on the page (the published Talluri–van Ryzin statement assumes nonnegative prices; this statement does not need them). Capacities are not bounded by $c$; the statement for every $x$ contains the one for $x\le c$.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1329, proof of Theorem 5, second sentence (citing Talluri and van Ryzin 2004)

import Mathlib
import Definitions.Def_MarkovChainChoice_SingleResource_ValueFunction
open MarkovChainChoice.Shared

namespace MarkovChainChoice.SingleResource

theorem marginal_value_monotone {n : ℕ} (M : Model n) (r : Fin n → ℝ) (T : ℕ)
    (hlam : ∑ j, M.lam j ≤ 1) :
    (∀ t x, 1 ≤ t → t ≤ T + 1 → 2 ≤ x →
        deltaValue M r T t x ≤ deltaValue M r T t (x - 1)) ∧
      ∀ t x, 1 ≤ t → t ≤ T → 1 ≤ x →
        deltaValue M r T (t + 1) x ≤ deltaValue M r T t x := by sorry

end MarkovChainChoice.SingleResource
