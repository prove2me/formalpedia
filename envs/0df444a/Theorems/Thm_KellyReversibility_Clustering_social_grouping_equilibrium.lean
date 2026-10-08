-- Prove2me | Theorems.Thm_KellyReversibility_Clustering_social_grouping_equilibrium
-- name    : KellyReversibility.Clustering.social_grouping_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:28:58.952663+00:00
-- url     : https://prove2.me/theorems/e2db176d-4c39-43bd-af4d-a317217836b9
-- title:
--   Eq. (8.2) — equilibrium of the social grouping model: $\pi(m) = B\prod_i \frac{1}{m_i!}\bigl(\frac{\beta}{\alpha\, i!}\bigr)^{m_i}$
-- statement:
--   Consider $M \ge 1$ individuals formed into groups, $m_i$ being the number of groups of $i$ individuals, so that
--   $$\sum_{i=1}^{M} i\, m_i = M. \qquad (8.1)$$
--   A given isolate joins a given group at rate $\alpha > 0$, and a given individual leaves its group (of size at least $2$) at rate $\beta > 0$; the resulting rates are those of the social grouping model of §8.1. Let $\mathcal S_M$ be the (finite) set of states satisfying (8.1). Then
--   $$\pi(m) = B \prod_{i=1}^{M} \frac{1}{m_i!} \Bigl(\frac{\beta}{\alpha\, i!}\Bigr)^{m_i}, \qquad m \in \mathcal S_M, \qquad (8.2)$$
--   with $B^{-1} = \sum_{m \in \mathcal S_M} \prod_i \frac{1}{m_i!}(\beta/(\alpha i!))^{m_i}$, satisfies the detailed balance conditions and the equilibrium equations for these rates on $\mathcal S_M$, is positive, and sums to $1$ over $\mathcal S_M$; it is the equilibrium distribution of the process.
--
--   This is the motivating example of the chapter, a special case of Theorem 8.1 with $c_i = \beta/(\alpha\, i!)$, and the distribution from which Exercise 8.2.1 computes the expected number of groups of each size.
--
--   **Formalization Note** Group sizes are the positive integers `ℕ+`; (8.2) is written with $c_i = \beta/(\alpha\, i!)$ in the product form of the closed process. The statement is at the level of rates; see Theorem 8.1.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 161–162, §8.1, Eq. (8.2) on the set (8.1)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Clustering_ClusteringRates

open KellyStochasticNetworks

namespace KellyReversibility.Clustering

theorem social_grouping_equilibrium (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (M : ℕ) (hM : 1 ≤ M) (S : Finset (ℕ+ →₀ ℕ)) (hS : ∀ m, m ∈ S ↔ unitCount m = M) :
    DetailedBalance
        (closedClusterPi (fun i : ℕ+ => β / (α * ((i : ℕ).factorial : ℝ))) S)
        (fun a b : S => socialRates α β a b) ∧
      FullBalance
        (closedClusterPi (fun i : ℕ+ => β / (α * ((i : ℕ).factorial : ℝ))) S)
        (fun a b : S => socialRates α β a b) ∧
      (∀ m : S, 0 < closedClusterPi (fun i : ℕ+ => β / (α * ((i : ℕ).factorial : ℝ))) S m) ∧
      ∑ m : S, closedClusterPi (fun i : ℕ+ => β / (α * ((i : ℕ).factorial : ℝ))) S m = 1 := by sorry

end KellyReversibility.Clustering
