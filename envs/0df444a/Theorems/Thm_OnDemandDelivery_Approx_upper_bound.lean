-- Prove2me | Theorems.Thm_OnDemandDelivery_Approx_upper_bound
-- name    : OnDemandDelivery.Approx.upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:40.946751+00:00
-- url     : https://prove2.me/theorems/8451dda3-5cc6-4651-8740-b426090ceb8e
-- title:
--   Appendix D, Proof of Theorem 1, part (2), p. 35 — a feasible static myopic policy costs at least E[ℋ_n], and for n < N some ω makes APT^n's value equal that cost
-- statement:
--   Consider the dispatching and routing model under its standing assumptions, a period $1 \le n < N$ and a driver status $\zeta^n$ with $\zeta^n_{n'} \le \bar K$ for $n \le n' \le N$. Let $\pi^{sm}$ be a static myopic policy, dispatching $K^{n',sm}$ drivers in period $n'$, that is feasible for $\mathbf{JDR}^n(\zeta^n)$, and let $J_n(\pi^{sm})$ denote its expected cost from $(n, \zeta^n)$. Then:
--   1. its expected cost is an upper bound of the expected cost-to-go,
--   $$\mathbb E_{\mathbb Q^n}\big[\mathcal H_n(\mathcal I^n, q^n, \zeta^n)\big] \le J_n(\pi^{sm});$$
--   2. there are nonnegative parameters $\omega^{n'}_m(K^m)$ for which the optimal value of $\mathbf{APT}^n(\zeta^n)$ equals that cost,
--   $$V^n_{APT}(\zeta^n) = J_n(\pi^{sm}).$$
--
--   Together with part (1) this gives the upper-bound half of Theorem 1: APT can be tuned to reproduce the cost of any feasible static myopic policy.
--
--   **Formalization Note.** The proof on p. 35 proposes $\omega^{n'}_m(K^{m,sm}) = 0$ and $\omega^{n'}_m(K) = \bar K + 1$ for $K \ne K^{m,sm}$. That choice does not constrain the last period's count from above by $K^{N,sm}$, and APT can then pick more drivers in period $N$ and fall below $J_n(\pi^{sm})$. A working choice is $\omega^N_n(K^{n,sm}) = \bar K - \zeta^n_N - K^{N,sm}$, the other $\omega^{n'}_m(K^{m,sm}) = 0$, and $\omega^{n'}_m(K) = \bar K + 1$ for $K \ne K^{m,sm}$. The statement asserts only that suitable parameters exist. It requires $n < N$: at $n = N$ the APT value is the last-period optimum, which can be strictly below the policy's cost. The policy's expected cost is defined recursively as the expected single-period cost of its decision plus the expected cost from the resulting state.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, p. 35, Appendix D, Proof of Theorem 1, part (2)

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

open scoped ENNReal NNReal

namespace OnDemandDelivery.Approx
open Model
theorem upper_bound {L : Type*} [Fintype L] (M : Model L) (hM : M.Standing) (n : ℕ)
    (hn : 1 ≤ n) (hnN : n < M.N) (ζ : ℕ → ℕ) (hζ : ∀ n', n ≤ n' → n' ≤ M.N → ζ n' ≤ M.Kbar)
    (π : M.StaticMyopic) (hπ : π.Feasible n ζ) :
    M.EH n ζ ≤ π.cost n ζ ∧ ∃ ω : ℕ → ℕ → ℕ → ℝ≥0, M.Vapt n ζ ω = π.cost n ζ := by sorry
end OnDemandDelivery.Approx
