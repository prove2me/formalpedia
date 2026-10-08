-- Prove2me | Theorems.Thm_KellyReversibility_Clustering_closed_clustering_reversible
-- name    : KellyReversibility.Clustering.closed_clustering_reversible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:28:50.497389+00:00
-- url     : https://prove2.me/theorems/626219e3-6105-40c9-a1d1-59d037325c67
-- title:
--   Theorem 8.1 — the closed clustering process is reversible with equilibrium $B\prod_r c_r^{m_r}/m_r!$
-- statement:
--   Let $\lambda_{rsu} \ge 0$, $\mu_{rsu} \ge 0$ be the parameters of the clustering rates (8.3), symmetric in $r$ and $s$, over a countable set of cluster types, and let $\mathcal S$ be the state space of a closed clustering process: a finite non-empty set of states, closed under the transitions of positive rate and irreducible. If there exist positive numbers $c_1, c_2, \dots$ satisfying
--   $$c_r c_s \lambda_{rsu} = c_u \mu_{rsu} \qquad (8.4)$$
--   then
--   $$\pi(m) = B \prod_r \frac{c_r^{m_r}}{m_r!}, \qquad m \in \mathcal S, \qquad (8.5)$$
--   with $B$ the normalizing constant, $B^{-1} = \sum_{m \in \mathcal S} \prod_r c_r^{m_r}/m_r!$, is the equilibrium distribution of the process and the process is reversible: on $\mathcal S$,
--
--   1. $\pi(m) q(m, m') = \pi(m') q(m', m)$ for all $m, m' \in \mathcal S$ (detailed balance);
--   2. $\pi(m) \sum_{m'} q(m, m') = \sum_{m'} \pi(m') q(m', m)$ for all $m \in \mathcal S$ (the equilibrium equations);
--   3. $\pi(m) > 0$ for every $m \in \mathcal S$, and $\sum_{m \in \mathcal S} \pi(m) = 1$.
--
--   The theorem turns the search for the equilibrium of a closed clustering process into the solution of the algebraic system (8.4), one equation per union/break-up pair.
--
--   **Formalization Note** The statement is at the level of rates: reversibility of the stationary process is recorded as detailed balance for a positive normalized $\pi$ (the equivalence of the two is Kelly's Theorem 1.3); that $\pi$ is the law of a stationary Markov process with these rates is not formalized. The process is the rate function (8.3) restricted to $\mathcal S$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 163, Theorem 8.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Clustering_ClusteringRates

open KellyStochasticNetworks

namespace KellyReversibility.Clustering

theorem closed_clustering_reversible {R : Type*} [LinearOrder R] [Countable R]
    (lam mu : R → R → R → ℝ) (c : R → ℝ) (S : Finset (R →₀ ℕ))
    (hlam : ∀ r s u, 0 ≤ lam r s u) (hmu : ∀ r s u, 0 ≤ mu r s u)
    (hlam_symm : ∀ r s u, lam r s u = lam s r u) (hmu_symm : ∀ r s u, mu r s u = mu s r u)
    (hS : IsClosedClusteringStateSpace (clusterRates lam mu) S)
    (hc : ∀ r, 0 < c r)
    (h84 : ∀ r s u, c r * c s * lam r s u = c u * mu r s u) :
    DetailedBalance (closedClusterPi c S) (fun a b : S => clusterRates lam mu a b) ∧
      FullBalance (closedClusterPi c S) (fun a b : S => clusterRates lam mu a b) ∧
      (∀ m : S, 0 < closedClusterPi c S m) ∧
      ∑ m : S, closedClusterPi c S m = 1 := by sorry

end KellyReversibility.Clustering
