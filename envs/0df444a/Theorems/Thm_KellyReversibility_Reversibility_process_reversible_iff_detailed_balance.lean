-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_process_reversible_iff_detailed_balance
-- name    : KellyReversibility.Reversibility.process_reversible_iff_detailed_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:40.373867+00:00
-- url     : https://prove2.me/theorems/17fb68a3-b089-440a-abee-50abb5e6e829
-- title:
--   Theorem 1.3 — a stationary Markov process is reversible iff detailed balance (1.6) holds
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be a stationary Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)\ge 0$ ($q(j,j)=0$), irreducible, with equilibrium distribution $\pi_0$. Then:
--
--   1. $X$ is reversible if and only if there exists a collection of positive numbers $\pi(j)$, $j\in\mathcal S$, summing to unity that satisfy the detailed balance conditions
--   $$\pi(j)q(j,k)=\pi(k)q(k,j),\qquad j,k\in\mathcal S; \tag{1.6}$$
--   2. when such a collection exists, it is the equilibrium distribution: $\pi=\pi_0$.
--
--   This is the basic tool of the book: an equilibrium distribution is found by solving the detailed balance conditions, and when they are solvable the process is reversible.
--
--   **Formalization Note** The process is the stationary Markov process with finite-dimensional distributions $\pi_0(j_1)\prod_r e^{(t_{r+1}-t_r)Q}(j_r,j_{r+1})$; reversibility is invariance of these under time reversal $t\mapsto\tau-t$, not detailed balance. The state space is finite (Kelly allows a countable one).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 6–7, Theorem 1.3

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

namespace KellyReversibility.Reversibility

/-- Theorem 1.3 (Kelly, pp. 6–7). -/
theorem process_reversible_iff_detailed_balance {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π₀ : S → ℝ) (hπ₀ : IsEquilibrium π₀ q) :
    (ProcessReversible q π₀ ↔
      ∃ π : S → ℝ, (∀ j, 0 < π j) ∧ ∑ j, π j = 1 ∧
        KellyStochasticNetworks.DetailedBalance π q) ∧
    ∀ π : S → ℝ, (∀ j, 0 < π j) → ∑ j, π j = 1 →
      KellyStochasticNetworks.DetailedBalance π q → π = π₀ := by sorry

end KellyReversibility.Reversibility
