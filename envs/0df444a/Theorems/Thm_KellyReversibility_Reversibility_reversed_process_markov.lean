-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_reversed_process_markov
-- name    : KellyReversibility.Reversibility.reversed_process_markov
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:58.240975+00:00
-- url     : https://prove2.me/theorems/cc0b879e-a5c1-4a8f-b464-0fe42a82aea5
-- title:
--   Theorem 1.12 — the reversed process is stationary Markov with rates $q'(j,k)=\pi(k)q(k,j)/\pi(j)$
-- statement:
--   Let $X(t)$ be a stationary Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)$ ($q(j,j)=0$), irreducible, and equilibrium distribution $\pi$. Then the reversed process $X(\tau-t)$ is a stationary Markov process with transition rates
--   $$q'(j,k)=\frac{\pi(k)q(k,j)}{\pi(j)},\qquad j,k\in\mathcal S,$$
--   and the same equilibrium distribution $\pi$.
--
--   The theorem holds whether or not $X$ is reversible; it identifies the time reversal of any stationary Markov process.
--
--   **Formalization Note** The conclusion has two parts: $\pi$ is an equilibrium distribution for $q'$, and for every $\tau$ the finite-dimensional distributions of $X(\tau-t)$ coincide with those of the stationary Markov process with rates $q'$ and equilibrium distribution $\pi$, i.e. $P(X(\tau-t_r)=j_r,\ r=0,\dots,n)$ equals the corresponding probability for that process at times $t_r$. The rates $q'$ are `reversedRates` of the published file `KellyStochasticNetworks_Balance`. The state space is finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 28, Theorem 1.12

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

namespace KellyReversibility.Reversibility

/-- Theorem 1.12 (Kelly, p. 28). -/
theorem reversed_process_markov {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibrium π q) :
    IsEquilibrium π (KellyStochasticNetworks.reversedRates π q) ∧
      ∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S) (τ : ℝ),
        fdd (transition q) π (fun r => τ - t r) j =
          fdd (transition (KellyStochasticNetworks.reversedRates π q)) π t j := by sorry

end KellyReversibility.Reversibility
