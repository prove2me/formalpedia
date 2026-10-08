-- Prove2me | Theorems.Thm_KellyReversibility_Clustering_product_form_detailed_balance
-- name    : KellyReversibility.Clustering.product_form_detailed_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:28:42.850311+00:00
-- url     : https://prove2.me/theorems/7b868d95-591c-4d2a-a8a6-006cd2f58162
-- title:
--   Eq. (8.6) — the product form $\prod_r c_r^{m_r}/m_r!$ satisfies detailed balance for the clustering rates (8.3)
-- statement:
--   Let cluster types $r$ range over a countable set, and let $\lambda_{rsu} \ge 0$ and $\mu_{rsu} \ge 0$ be union and break-up parameters with $\lambda_{rsu} = \lambda_{sru}$ and $\mu_{rsu} = \mu_{sru}$. Let $q$ be the transition rates (8.3) of the clustering process on the states $m = (m_r)$ with finitely many non-zero entries. Suppose there are positive numbers $c_r$ satisfying (8.4),
--   $$c_r c_s \lambda_{rsu} = c_u \mu_{rsu} \qquad \text{for all } r, s, u.$$
--   Then $\Phi(m) = \prod_r c_r^{m_r}/m_r!$ satisfies the detailed balance conditions (8.6):
--   $$\Phi(m)\, q(m, m') = \Phi(m')\, q(m', m) \qquad \text{for all states } m, m'.$$
--
--   This is the computation behind both Theorem 8.1 and Theorem 8.2: the balance is local, union against the break-up that undoes it, so it holds on the whole state space before any restriction to a closed class or any normalization.
--
--   **Formalization Note** The identity is stated for the aggregated rate $q(m, m')$ of the definition, the sum over every union and break-up taking $m$ to $m'$; no normalization of $\Phi$ is involved.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 163, proof of Theorem 8.1, Eq. (8.6) under (8.4)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Clustering_ClusteringRates

open KellyStochasticNetworks

namespace KellyReversibility.Clustering

theorem product_form_detailed_balance {R : Type*} [LinearOrder R] [Countable R]
    (lam mu : R → R → R → ℝ) (c : R → ℝ)
    (hlam : ∀ r s u, 0 ≤ lam r s u) (hmu : ∀ r s u, 0 ≤ mu r s u)
    (hlam_symm : ∀ r s u, lam r s u = lam s r u) (hmu_symm : ∀ r s u, mu r s u = mu s r u)
    (hc : ∀ r, 0 < c r)
    (h84 : ∀ r s u, c r * c s * lam r s u = c u * mu r s u) :
    DetailedBalance (productWeight c) (clusterRates lam mu) := by sorry

end KellyReversibility.Clustering
