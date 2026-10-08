-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_tree_graph_reversible
-- name    : KellyReversibility.Reversibility.tree_graph_reversible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:48.858656+00:00
-- url     : https://prove2.me/theorems/62a78285-2293-4dd2-b7ef-bf911fd380a7
-- title:
--   Lemma 1.5 — a stationary Markov process whose graph is a tree is reversible
-- statement:
--   Let $X(t)$ be a stationary Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)$ ($q(j,j)=0$), irreducible, with equilibrium distribution $\pi$. Let $G$ be the graph associated with the process: vertices $\mathcal S$, and an edge joining distinct $j,k$ if $q(j,k)>0$ or $q(k,j)>0$. If $G$ is a tree, then the process is reversible.
--
--   No condition on the rates is needed beyond the shape of $G$: any birth and death process, for instance, is reversible.
--
--   **Formalization Note** "Reversible" is the distributional property of p. 5 for the stationary process with equilibrium distribution $\pi$. "Tree" is a connected acyclic simple graph. Unlike the platform's rate-level `SerfozoStochasticNetworks.tree_reversible`, no two-way communication hypothesis is assumed: it follows from the equilibrium. The state space is finite (Kelly allows a countable one).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 9, Lemma 1.5 (graph G defined on p. 8)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

namespace KellyReversibility.Reversibility

/-- Lemma 1.5 (Kelly, p. 9). -/
theorem tree_graph_reversible {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibrium π q) (htree : (rateGraph q).IsTree) :
    ProcessReversible q π := by sorry

end KellyReversibility.Reversibility
