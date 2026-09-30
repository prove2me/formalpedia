-- Prove2me | Theorems.Thm_KellyStochasticNetworks_closed_migration_equilibrium
-- name    : KellyStochasticNetworks.closed_migration_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:25:52.294515+00:00
-- url     : https://prove2.me/theorems/fe9b6a0a-4f15-4352-acc5-ec4b84e40178
-- title:
--   Theorem 2.4 — the product form of a closed migration process
-- statement:
--   Consider a **closed migration process** on $J$ colonies: individuals move one at a time from
--   colony $j$ to colony $k$ at rate
--   $$q(n, T^{jk}n) = \lambda_{jk}\,\varphi_j(n_j),$$
--   where $\lambda_{jj} = 0$, all $\lambda_{jk} \ge 0$, $\varphi_j(0) = 0$ and $\varphi_j(r) > 0$
--   for $r \ge 1$. Let $(\alpha_j)$ solve the traffic equations (2.1):
--   $$\alpha_j > 0, \qquad \sum_j \alpha_j = 1, \qquad
--     \alpha_j \sum_k \lambda_{jk} = \sum_k \alpha_k \lambda_{kj}.$$
--
--   Then for any non-zero constant $G$ the measure
--   $$\pi(n) = G^{-1}\prod_{j=1}^{J}\frac{\alpha_j^{\,n_j}}{\prod_{r=1}^{n_j}\varphi_j(r)}$$
--   satisfies the equilibrium equations for these rates. On the state space
--   $S = \{n : \sum_j n_j = N\}$ of a closed process with $N$ individuals, $G$ is the normalizing
--   constant $G_N$ that makes $\pi$ a probability distribution, and $\pi$ is then the equilibrium
--   distribution of the process.
--
--   The striking feature is that the joint distribution factorizes as a product over individual
--   colonies, even though the total population is held fixed and the occupancies are therefore
--   dependent.
--
--   **Formalization Note** The equilibrium equations are a local condition, one equation per
--   state, so they are stated over all of $\mathbb{Z}_+^J$ rather than over the fixed-population
--   subset; restricting to $S$ changes nothing, because every transition preserves $\sum_j n_j$.
--   The constant $G$ is left free precisely because the equilibrium equations are homogeneous:
--   fixing it is the separate normalization step over $S$.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 27 (PDF p. 35), Theorem 2.4: 'The equilibrium distribution for a closed migration process is pi(n) = G_N^{-1} prod_{j=1}^{J} alpha_j^{n_j} / prod_{r=1}^{n_j} phi_j(r), n in S. Here, G_N is a normalizing constant, chosen so the distribution sums to 1, and (alpha_j) are the solution to the traffic equations (2.1).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyStochasticNetworks

theorem closed_migration_equilibrium {J : ℕ} (lam : Fin J → Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (α : Fin J → ℝ) (G : ℝ) (hG : G ≠ 0)
    (hlamdiag : ∀ j, lam j j = 0) (hlam : ∀ j k, 0 ≤ lam j k)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (htraffic : ClosedTraffic lam α) :
    FullBalance (fun n : Fin J → ℕ => G⁻¹ * ∏ j, (α j ^ n j / phiProd φ j (n j)))
      (closedMigrationRates lam φ) := by sorry

end KellyStochasticNetworks
