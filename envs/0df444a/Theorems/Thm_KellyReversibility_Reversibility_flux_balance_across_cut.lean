-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_flux_balance_across_cut
-- name    : KellyReversibility.Reversibility.flux_balance_across_cut
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:38.162583+00:00
-- url     : https://prove2.me/theorems/6f2c106b-63c8-4e16-8e75-635e8d534992
-- title:
--   Lemma 1.4 — probability flux across a cut balances (1.8)
-- statement:
--   Let $X(t)$ be a stationary Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)$, irreducible, with equilibrium distribution $\pi$. The probability flux each way across a cut balances: for every $\mathcal A\subseteq\mathcal S$,
--   $$\sum_{j\in\mathcal A}\sum_{k\in\mathcal S-\mathcal A}\pi(j)q(j,k)=\sum_{j\in\mathcal A}\sum_{k\in\mathcal S-\mathcal A}\pi(k)q(k,j). \tag{1.8}$$
--
--   For $\mathcal A=\{j\}$ this is the equilibrium equation (1.3) at $j$; the lemma holds whether or not the process is reversible, and it is the input to Lemma 1.5.
--
--   **Formalization Note** The state space is finite, so every sum is a finite sum (Kelly allows a countable state space).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 8, Lemma 1.4, Eq. (1.8)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

namespace KellyReversibility.Reversibility

/-- Lemma 1.4 (Kelly, p. 8), equation (1.8). -/
theorem flux_balance_across_cut {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibrium π q) (A : Finset S) :
    ∑ j ∈ A, ∑ k ∈ Aᶜ, π j * q j k = ∑ j ∈ A, ∑ k ∈ Aᶜ, π k * q k j := by sorry

end KellyReversibility.Reversibility
