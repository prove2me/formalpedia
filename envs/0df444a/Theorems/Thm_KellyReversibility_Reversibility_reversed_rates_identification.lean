-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_reversed_rates_identification
-- name    : KellyReversibility.Reversibility.reversed_rates_identification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:36:08.274134+00:00
-- url     : https://prove2.me/theorems/069d5c49-e20e-4159-8cc9-af14490b3271
-- title:
--   Theorem 1.13 — guessing the reversed rates: (1.27) and (1.28) identify the reversed process and the equilibrium
-- statement:
--   Let $X(t)$ be a stationary Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)$ ($q(j,j)=0$), irreducible, and write $q(j)=\sum_k q(j,k)$. Suppose there are numbers $q'(j,k)$, $j,k\in\mathcal S$, with $q'(j)=\sum_k q'(j,k)$, such that
--   $$q'(j)=q(j),\qquad j\in\mathcal S, \tag{1.27}$$
--   and a collection of positive numbers $\pi(j)$, $j\in\mathcal S$, summing to unity, such that
--   $$\pi(j)q(j,k)=\pi(k)q'(k,j),\qquad j,k\in\mathcal S. \tag{1.28}$$
--   Then $q'(j,k)$ are the transition rates of the reversed process $X(\tau-t)$, and $\pi$ is the equilibrium distribution of both processes.
--
--   This is the converse of Theorem 1.12 and the practical method of Chapter 3: guess the reversed process, check (1.27) and (1.28), and the equilibrium distribution follows.
--
--   **Formalization Note** The conclusion states that $\pi$ is an equilibrium distribution for $q$ and for $q'$, and that for every $\tau$ the finite-dimensional distributions of $X(\tau-t)$, where $X$ is the stationary process with rates $q$ and equilibrium distribution $\pi$, equal those of the stationary process with rates $q'$ and equilibrium distribution $\pi$. Non-negativity of $q'$ is not assumed; it follows from (1.28). The state space is finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 30, Theorem 1.13, Eqs. (1.27), (1.28)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

namespace KellyReversibility.Reversibility

/-- Theorem 1.13 (Kelly, p. 30). -/
theorem reversed_rates_identification {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (q' : S → S → ℝ) (h127 : ∀ j, ∑ k, q' j k = ∑ k, q j k)
    (π : S → ℝ) (hπpos : ∀ j, 0 < π j) (hπ1 : ∑ j, π j = 1)
    (h128 : ∀ j k, π j * q j k = π k * q' k j) :
    IsEquilibrium π q ∧ IsEquilibrium π q' ∧
      ∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S) (τ : ℝ),
        fdd (transition q) π (fun r => τ - t r) j = fdd (transition q') π t j := by sorry

end KellyReversibility.Reversibility
