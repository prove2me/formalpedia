-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_altered_rates_reversible
-- name    : KellyReversibility.Reversibility.altered_rates_reversible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:51.762783+00:00
-- url     : https://prove2.me/theorems/428a64f7-9e63-497d-b0a0-0468b8775665
-- title:
--   Lemma 1.9 — scaling the rates out of $\mathcal A$ by $c>0$ preserves reversibility
-- statement:
--   Let $X(t)$ be a reversible stationary Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)$ ($q(j,j)=0$), irreducible, with equilibrium distribution $\pi$. Let $\mathcal A\subseteq\mathcal S$ and $c>0$, and alter the rates by changing $q(j,k)$ to $cq(j,k)$ for $j\in\mathcal A$, $k\in\mathcal S-\mathcal A$. Then the resulting Markov process is reversible in equilibrium and has equilibrium distribution
--   $$\pi'(j)=\begin{cases}B\pi(j), & j\in\mathcal A,\\ Bc\pi(j), & j\in\mathcal S-\mathcal A,\end{cases}\qquad B^{-1}=\sum_{j\in\mathcal A}\pi(j)+c\sum_{j\in\mathcal S-\mathcal A}\pi(j).$$
--
--   The lemma is a source of non-trivial reversible processes built from simple ones.
--
--   **Formalization Note** The conclusion asserts that $\pi'$ is an equilibrium distribution of the altered rates (positive, summing to one, satisfying (1.3)) and that the stationary process with the altered rates and $\pi'$ is reversible in the distributional sense of p. 5. The normalizing constant is the one in the proof on p. 25. The state space is finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 25, Lemma 1.9

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

namespace KellyReversibility.Reversibility

/-- Lemma 1.9 (Kelly, p. 25). -/
theorem altered_rates_reversible {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibrium π q) (hrev : ProcessReversible q π)
    (A : Finset S) (c : ℝ) (hc : 0 < c) :
    IsEquilibrium (alteredEquilibrium π A c) (alteredRates q A c) ∧
      ProcessReversible (alteredRates q A c) (alteredEquilibrium π A c) := by sorry

end KellyReversibility.Reversibility
