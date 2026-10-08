-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_compensator_identities
-- name    : GVRPricing.FixedPrice.compensator_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:59:46.811781+00:00
-- url     : https://prove2.me/theorems/43b2ccb4-64a4-467a-91cb-4fe63950d1c6
-- title:
--   Eqs. (13)–(14) — E_u[N_t] = E_u[∫λ_s ds] ≤ n and J_u(n,t) = E_u[∫r(λ_s) ds] for every policy
-- statement:
--   Let $u$ be an admissible pricing policy, $n$ an initial stock and $t\ge0$ a horizon. Let $N_s$ be the number of sales by time $s$ and $\lambda_s$ the intensity in force at time $s$ (zero once the stock is exhausted). Then
--   $$E_u\Big[\int_0^t dN_s\Big]=E_u\Big[\int_0^t\lambda_s\,ds\Big]\le n\qquad(13)$$
--   and
--   $$J_u(n,t)=E_u\Big[\int_0^t p_s\,dN_s\Big]=E_u\Big[\int_0^t r(\lambda_s)\,ds\Big].\qquad(14)$$
--
--   These identities replace the random revenue, collected at the jump times of the sales process, by integrals of its intensity. They are the probabilistic step of the proof of Theorem 2, and they let a deterministic rate path be compared with any stochastic policy.
--
--   **Formalization Note** All quantities are in $[0,\infty]$. The page derives (13) after quoting Proposition 1 ($\lambda_s\le\lambda^*$ for the optimal intensity); for an arbitrary policy no such bound holds when $\Lambda$ is unbounded, and none is needed. At most $n$ sales occur, so both sides of (13) are at most $n$, and both sides of (14) are equal as elements of $[0,\infty]$. The page's restriction to Markovian policies is not made: the identities are stated for every non-anticipating policy.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1007 (PDF 9), §3.2.1, Proof of Theorem 2, eqs. (13)–(14)

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- **Eqs. (13)–(14)** (§3.2.1, Proof of Theorem 2, p. 1007). For every admissible policy `u`,
initial stock `n` and horizon `t ≥ 0` (elapsed time):
* (13) `E_u[∫_0^t dN_s] = E_u[∫_0^t λ_s ds] ≤ n`;
* (14) `J_u(n, t) = E_u[∫_0^t r(λ_s) ds]`,
where `N` is the controlled sales process and `λ_s` the intensity in force at time `s` (`0`
after the `n`-th sale). No bound `λ_s ≤ λ*` is assumed. -/
theorem compensator_identities (M : Model) (u : Policy M) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    u.expectedSales n t = u.expectedCumIntensity n t ∧
    u.expectedCumIntensity n t ≤ n ∧
    u.expectedRevenue n t = u.expectedRevenueRate n t := by sorry

end GVRPricing.FixedPrice
