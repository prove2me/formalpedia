-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_truncated_process_reversible
-- name    : KellyReversibility.Reversibility.truncated_process_reversible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:57.705171+00:00
-- url     : https://prove2.me/theorems/14805a17-7aea-4146-a8dc-91faae96287c
-- title:
--   Corollary 1.10 — a reversible process truncated to $\mathcal A$ is reversible with distribution $\pi(j)/\sum_{\mathcal A}\pi$
-- statement:
--   Let $X(t)$ be a reversible stationary Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)$ ($q(j,j)=0$), irreducible, with equilibrium distribution $\pi$. Let $\mathcal A\subseteq\mathcal S$ be nonempty and truncate the process to $\mathcal A$: the rates $q(j,k)$, $j\in\mathcal A$, $k\in\mathcal S-\mathcal A$, are changed to zero, and the resulting process on $\mathcal A$ is assumed irreducible within $\mathcal A$. Then the truncated process is reversible in equilibrium and has equilibrium distribution
--   $$\frac{\pi(j)}{\sum_{k\in\mathcal A}\pi(k)},\qquad j\in\mathcal A.$$
--
--   The truncated process is in equilibrium distributed as the original one conditioned on being in $\mathcal A$; loss networks and queues with a shared waiting room are examples.
--
--   **Formalization Note** The truncated process lives on the subtype $\mathcal A$ with the rates `truncatedRates q A` of the published file `KellyStochasticNetworks_LossNetwork` (rates between states of $\mathcal A$ unchanged; transitions leaving $\mathcal A$ have no target). Irreducibility within $\mathcal A$ is the hypothesis in Kelly's definition of truncation (p. 25). Reversibility is the distributional property of p. 5. The state space is finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 26, Corollary 1.10 (truncation defined on p. 25)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyReversibility.Reversibility

/-- Corollary 1.10 (Kelly, p. 26). -/
theorem truncated_process_reversible {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibrium π q) (hrev : ProcessReversible q π)
    (A : Set S) [DecidablePred (· ∈ A)] (hA : A.Nonempty)
    (hirrA : RatesIrreducible (KellyStochasticNetworks.truncatedRates q A)) :
    IsEquilibrium (fun j : A => π j / ∑ k : A, π k) (KellyStochasticNetworks.truncatedRates q A) ∧
      ProcessReversible (KellyStochasticNetworks.truncatedRates q A)
        (fun j : A => π j / ∑ k : A, π k) := by sorry

end KellyReversibility.Reversibility
