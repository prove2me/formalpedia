-- Prove2me | Theorems.Thm_KellyStochasticNetworks_open_migration_reversed
-- name    : KellyStochasticNetworks.open_migration_reversed
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:27:10.394748+00:00
-- url     : https://prove2.me/theorems/343c31b8-4a36-4927-b374-a702d378263c
-- title:
--   Theorem 2.9 — the reversed process is an open migration process
-- statement:
--   An open migration process is **not** reversible in general — the detailed balance equations
--   fail — but it behaves well under time reversal. Let $\pi$ be its product-form equilibrium
--   distribution and let
--   $$q'(n,m) = \frac{\pi(m)\,q(m,n)}{\pi(n)}$$
--   be the transition rates of the reversed process, as computed in Proposition 1.1. Then $q'$ is
--   again of open-migration form, with the three rate families
--
--   1. $q'(n, T^{jk}n) = \lambda'_{jk}\,\varphi_j(n_j)$ for $j \ne k$ and $n_j \ge 1$, where
--      $\displaystyle \lambda'_{jk} = \frac{\alpha_k}{\alpha_j}\lambda_{kj}$;
--   2. $q'(n, T^{j\to}n) = \mu'_j\,\varphi_j(n_j)$ for $n_j \ge 1$, where
--      $\displaystyle \mu'_j = \frac{\nu_j}{\alpha_j}$;
--   3. $q'(n, T^{\to k}n) = \nu'_k$, where $\nu'_k = \alpha_k \mu_k$.
--
--   The same functions $\varphi_j$ appear, so the reversed process is an open migration process
--   with the same service mechanism and rerouted traffic. Because the reversed departure stream
--   from colony $k$ is the forward immigration stream into it, the third identity is what yields
--   Corollary 2.10: the exit process from colony $k$ is Poisson of rate $\alpha_k\mu_k$.
--
--   **Formalization Note** The three identities are stated pointwise rather than as an equality of
--   rate matrices, with $j \ne k$ and $n_j \ge 1$ where the target state must be a genuine state of
--   $\mathbb{Z}_+^J$. The rate matrix is the assembled one, so each identity also asserts that no
--   other transition of the original process happens to land on the same state with a non-zero
--   rate.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 32-33 (PDF pp. 40-41), Theorem 2.9: 'If (n(t), t in R) is a stationary open migration process, then so is the reversed process (n(-t), t in R).' Proof: 'Using Proposition 1.1, we have q'(n, T^{jk}n) = ... = lambda'_{jk} phi_j(n_j), where lambda'_{jk} = (alpha_k/alpha_j) lambda_{kj}. Similarly we find (check this) that the remaining transition rates of the reversed open migration process have the form q'(n, T^{j->}n) = mu'_j phi_j(n_j), q'(n, T^{->k}n) = nu'_k, where mu'_j = nu_j/alpha_j and nu'_k = alpha_k mu_k.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyStochasticNetworks

theorem open_migration_reversed {J : ℕ} (lam : Fin J → Fin J → ℝ)
    (mu nu α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (hlamdiag : ∀ j, lam j j = 0)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hα : ∀ j, 0 < α j) (hg : ∀ j, 0 < g j) :
    (∀ (n : Fin J → ℕ) (j k : Fin J), j ≠ k → 1 ≤ n j →
        reversedRates (openMigrationPi α g φ) (openMigrationRates lam mu nu φ) n (Tjk j k n)
          = (α k * lam k j / α j) * φ j (n j))
      ∧ (∀ (n : Fin J → ℕ) (j : Fin J), 1 ≤ n j →
        reversedRates (openMigrationPi α g φ) (openMigrationRates lam mu nu φ) n (Tout j n)
          = (nu j / α j) * φ j (n j))
      ∧ (∀ (n : Fin J → ℕ) (k : Fin J),
        reversedRates (openMigrationPi α g φ) (openMigrationRates lam mu nu φ) n (Tin k n)
          = α k * mu k) := by sorry

end KellyStochasticNetworks
