-- Prove2me | Theorems.Thm_KellyReversibility_Clustering_poisson_product_normalization
-- name    : KellyReversibility.Clustering.poisson_product_normalization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:28:52.879851+00:00
-- url     : https://prove2.me/theorems/9cd1c8ec-148e-4ce1-8e8f-7a2ce9ddee88
-- title:
--   Eq. (8.9) — $\sum_r c_r < \infty$ is necessary and sufficient for the product form (8.10) to be a probability on finite states
-- statement:
--   Let $c_r > 0$ for each cluster type $r$ in a countable set, and let $\mathcal S$ be the countable set of states $m = (m_r)$ with $\sum_r m_r$ finite. Then:
--
--   1. the product-form weights $\prod_r c_r^{m_r}/m_r!$ are summable over $\mathcal S$ if and only if
--   $$\sum_r c_r < \infty; \qquad (8.9)$$
--   2. under (8.9), the form (8.10),
--   $$\pi(m) = \prod_r e^{-c_r} \frac{c_r^{m_r}}{m_r!},$$
--   assigns total probability one to $\mathcal S$: $\sum_{m \in \mathcal S} \pi(m) = 1$.
--
--   This is the role the book assigns to (8.9) in the proof of Theorem 8.2: the extra assumption is exactly what lets the product form be normalized on the countable state space of the open clustering process.
--
--   **Formalization Note** Necessity is stated for the unnormalized weights, since without (8.9) the infinite product (8.10) converges to $0$ for every state, so it is not a probability on $\mathcal S$. Summability is unconditional summability over finitely supported vectors `R →₀ ℕ`.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 164, proof of Theorem 8.2 (role of (8.9) for (8.10))

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Clustering_ClusteringRates

open KellyStochasticNetworks

namespace KellyReversibility.Clustering

theorem poisson_product_normalization {R : Type*} [LinearOrder R] [Countable R]
    (c : R → ℝ) (hc : ∀ r, 0 < c r) :
    (Summable c ↔ Summable (productWeight c)) ∧
      (Summable c → HasSum (openClusterPi c) 1) := by sorry

end KellyReversibility.Clustering
