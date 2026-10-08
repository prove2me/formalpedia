-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_chain_kolmogorov_criterion
-- name    : KellyReversibility.Reversibility.chain_kolmogorov_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:25.408521+00:00
-- url     : https://prove2.me/theorems/dae7dff4-5b0a-4c44-96eb-02b2eecdda8d
-- title:
--   Theorem 1.7 — Kolmogorov's criterion (1.21) for a stationary Markov chain
-- statement:
--   Let $X(t)$, $t\in\mathbb Z$, be a stationary Markov chain on a finite state space $\mathcal S$ with transition probabilities $p(j,k)$, irreducible, with equilibrium distribution $\pi_0$. The chain is reversible if and only if its transition probabilities satisfy
--   $$p(j_1,j_2)p(j_2,j_3)\cdots p(j_{n-1},j_n)p(j_n,j_1)=p(j_1,j_n)p(j_n,j_{n-1})\cdots p(j_3,j_2)p(j_2,j_1) \tag{1.21}$$
--   for any finite sequence of states $j_1,j_2,\dots,j_n\in\mathcal S$.
--
--   The criterion decides reversibility from the transition probabilities alone, without knowing the equilibrium distribution.
--
--   **Formalization Note** Reversibility is the distributional property of p. 5 for the stationary chain started in $\pi_0$. The sequences in (1.21) have arbitrary length and may repeat states. The state space is finite (Kelly allows a countable one).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 21, Theorem 1.7, Eq. (1.21)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovChain

namespace KellyReversibility.Reversibility

/-- Theorem 1.7 (Kelly, p. 21). -/
theorem chain_kolmogorov_criterion {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (hP : MarkovMixing.IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π₀ : S → ℝ) (hπ₀ : IsChainEquilibrium P π₀) :
    ChainReversible P π₀ ↔ KolmogorovCycle P := by sorry

end KellyReversibility.Reversibility
