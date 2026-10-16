-- Prove2me | Theorems.Thm_OnDemandDelivery_Approx_last_period
-- name    : OnDemandDelivery.Approx.last_period
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:56.866104+00:00
-- url     : https://prove2.me/theorems/0afb70ea-4d25-49b6-9a4a-5523a12342bd
-- title:
--   Appendix D, Proof of Theorem 1, p. 35 — at n = N, E[ℋ_N] = min over K^N ≤ K̄ − ζ^N_N of E[ℋ^s(K^N, ·)]
-- statement:
--   Consider the dispatching and routing model under its standing assumptions and a driver status $\zeta^N$ in the last period with $\zeta^N_N \le \bar K$. Then the expected last-period cost-to-go equals the best expected single-period cost over the admissible numbers of dispatched drivers:
--   $$\mathbb E_{\mathbb Q^N}\big[\mathcal H_N(\mathcal I^N, q^N, \zeta^N)\big] = \min_{K^N \in \mathbb N,\ K^N \le \bar K - \zeta^N_N} \mathbb E_{\mathbb Q^N}\big[\mathcal H^s(K^N, \mathcal I^N, q^N)\big].$$
--
--   The right-hand side is the problem $\mathbf{APT}^N(\zeta^N)$, so this identity is the exactness of the approximation in the last period. Its content is that the minimum over the number of drivers may be taken outside the expectation, since in the last period it is optimal to use every available driver.
--
--   **Formalization Note.** $\mathcal H_N$ is defined directly by (8), as a minimum over single-period decisions feasible with $\bar K - \zeta^N_N$ available drivers, not through the right-hand side. Values are in $[0,\infty]$; the minimum on the right is an infimum over $K^N \in \mathbb N$ with $K^N \le \bar K - \zeta^N_N$ as real numbers.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, p. 35, Appendix D, Proof of Theorem 1, display after "Lastly, when n = N"

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

open scoped ENNReal NNReal

namespace OnDemandDelivery.Approx
open Model
theorem last_period {L : Type*} [Fintype L] (M : Model L) (hM : M.Standing) (ζ : ℕ → ℕ)
    (hζ : ζ M.N ≤ M.Kbar) :
    M.EH M.N ζ = ⨅ (K : ℕ) (_ : (K : ℝ) ≤ (M.Kbar : ℝ) - (ζ M.N : ℝ)), M.EHs M.N K := by sorry
end OnDemandDelivery.Approx
