-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_chain_reversible_iff_detailed_balance
-- name    : KellyReversibility.Reversibility.chain_reversible_iff_detailed_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:08.76359+00:00
-- url     : https://prove2.me/theorems/c63dec7c-d04b-442f-8a2e-8651cad3069a
-- title:
--   Theorem 1.2 — a stationary Markov chain is reversible iff detailed balance (1.5) holds
-- statement:
--   Let $X(t)$, $t\in\mathbb Z$, be a stationary Markov chain on a finite state space $\mathcal S$ with transition probabilities $p(j,k)$ (a stochastic matrix), irreducible, with equilibrium distribution $\pi_0$. Then:
--
--   1. $X$ is reversible if and only if there exists a collection of positive numbers $\pi(j)$, $j\in\mathcal S$, summing to unity that satisfy the detailed balance conditions
--   $$\pi(j)p(j,k)=\pi(k)p(k,j),\qquad j,k\in\mathcal S; \tag{1.5}$$
--   2. when such a collection exists, it is the equilibrium distribution: $\pi=\pi_0$.
--
--   This turns a statement about the joint laws of the chain at all finite sets of times into a finite system of equations.
--
--   **Formalization Note** Reversibility is the distributional definition of p. 5, read through the finite-dimensional distributions $\pi_0(j_1)\prod P^{t_{r+1}-t_r}(j_r,j_{r+1})$; it is not defined as detailed balance. The state space is finite (Kelly allows a countable one).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 5–6, Theorem 1.2

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovChain

namespace KellyReversibility.Reversibility

/-- Theorem 1.2 (Kelly, pp. 5–6). -/
theorem chain_reversible_iff_detailed_balance {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (hP : MarkovMixing.IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π₀ : S → ℝ) (hπ₀ : IsChainEquilibrium P π₀) :
    (ChainReversible P π₀ ↔
      ∃ π : S → ℝ, (∀ j, 0 < π j) ∧ ∑ j, π j = 1 ∧
        KellyStochasticNetworks.DetailedBalance π P) ∧
    ∀ π : S → ℝ, (∀ j, 0 < π j) → ∑ j, π j = 1 →
      KellyStochasticNetworks.DetailedBalance π P → π = π₀ := by sorry

end KellyReversibility.Reversibility
