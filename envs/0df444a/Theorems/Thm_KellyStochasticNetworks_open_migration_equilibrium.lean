-- Prove2me | Theorems.Thm_KellyStochasticNetworks_open_migration_equilibrium
-- name    : KellyStochasticNetworks.open_migration_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:29:34.142465+00:00
-- url     : https://prove2.me/theorems/93a57014-3f83-40de-81e3-f041dda13c7d
-- title:
--   Theorem 2.8 — the product form of an open migration process
-- statement:
--   Consider an **open migration process** on $J$ colonies. The state is the vector
--   $n = (n_1,\dots,n_J)$ of colony occupancies, and the transition rates are
--   $$q(n, T^{jk}n) = \lambda_{jk}\varphi_j(n_j), \qquad
--     q(n, T^{j\to}n) = \mu_j\varphi_j(n_j), \qquad
--     q(n, T^{\to k}n) = \nu_k,$$
--   where $T^{jk}$ moves one individual from colony $j$ to colony $k$, $T^{j\to}$ removes one from
--   colony $j$, and $T^{\to k}$ adds one to colony $k$. All rates are non-negative,
--   $\lambda_{jj} = 0$, and $\varphi_j(0) = 0$ with $\varphi_j(r) > 0$ for $r \ge 1$, so nothing
--   leaves an empty colony.
--
--   Let $(\alpha_j)$ be a positive solution of the traffic equations (2.2),
--   $$\alpha_j\Bigl(\mu_j + \sum_k \lambda_{jk}\Bigr) = \nu_j + \sum_k \alpha_k \lambda_{kj},$$
--   and suppose each series
--   $$g_j = \sum_{m=0}^{\infty}\frac{\alpha_j^{\,m}}{\prod_{r=1}^{m}\varphi_j(r)}$$
--   converges. Then
--   $$\pi(n) = \prod_{j=1}^{J}\pi_j(n_j), \qquad
--     \pi_j(m) = g_j^{-1}\,\frac{\alpha_j^{\,m}}{\prod_{r=1}^{m}\varphi_j(r)}$$
--   is the equilibrium distribution of the process: it satisfies the equilibrium equations, and it
--   sums to $1$ over the whole state space $\mathbb{Z}_+^{J}$.
--
--   The conclusion is that in equilibrium, at any fixed time, the occupancies
--   $n_1(t),\dots,n_J(t)$ are **independent**, each distributed as if its colony were fed by a
--   Poisson stream — although in most open migration networks they are not independent as
--   processes, and the arrival stream into a colony is not Poisson.
--
--   **Formalization Note** The convergence hypothesis $g_j < \infty$ and the value of $g_j$ are
--   asserted together as a single summability statement, one per colony. Both halves of the
--   conclusion are stated: the equilibrium equations alone are homogeneous and are satisfied by
--   every positive multiple of $\pi$, so the normalization is what pins the constants $g_j$ down.
--   The equilibrium equations are written against the assembled rate matrix, with sums over actual
--   states, so a transition out of an empty colony contributes nothing rather than being read
--   through truncated subtraction.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 31 (PDF p. 39), Theorem 2.8: 'Define the constants g_j = sum_{n=0}^{infinity} alpha_j^n / prod_{r=1}^{n} phi_j(r), j = 1, 2, ..., J. Theorem 2.8 If g_1, ..., g_J < infinity, then n has the equilibrium distribution pi(n) = prod_{j=1}^{J} pi_j(n_j), pi_j(n_j) = g_j^{-1} alpha_j^{n_j} / prod_{r=1}^{n_j} phi_j(r).' The traffic equations (2.2) are on the same page. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyStochasticNetworks

theorem open_migration_equilibrium {J : ℕ} (lam : Fin J → Fin J → ℝ)
    (mu nu α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (hlamdiag : ∀ j, lam j j = 0) (hlam : ∀ j k, 0 ≤ lam j k)
    (hmu : ∀ j, 0 ≤ mu j) (hnu : ∀ j, 0 ≤ nu j)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hα : ∀ j, 0 < α j) (htraffic : OpenTraffic lam mu nu α)
    (hg : ∀ j, HasSum (fun m : ℕ => α j ^ m / phiProd φ j m) (g j)) :
    FullBalance (openMigrationPi α g φ) (openMigrationRates lam mu nu φ)
      ∧ HasSum (openMigrationPi α g φ) 1 := by sorry

end KellyStochasticNetworks
