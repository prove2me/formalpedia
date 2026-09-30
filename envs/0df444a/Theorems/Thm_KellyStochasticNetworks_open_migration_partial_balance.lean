-- Prove2me | Theorems.Thm_KellyStochasticNetworks_open_migration_partial_balance
-- name    : KellyStochasticNetworks.open_migration_partial_balance
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:26:25.744163+00:00
-- url     : https://prove2.me/theorems/7ff74d8f-3984-44c4-829a-c4b2571d76a7
-- title:
--   Equations (2.3) and (2.4) — the partial balance equations
-- statement:
--   Let $\pi$ be the product-form measure
--   $\pi(n) = \prod_j g_j^{-1}\alpha_j^{\,n_j}/\prod_{r=1}^{n_j}\varphi_j(r)$
--   of an open migration process whose $(\alpha_j)$ solve the traffic equations (2.2). Two families
--   of **partial balance** equations hold.
--
--   1. *Colony balance, equation (2.3).* For every state $n$ and every colony $j$ with
--      $n_j \ge 1$,
--      $$\pi(n)\Bigl[\sum_k \lambda_{jk}\varphi_j(n_j) + \mu_j\varphi_j(n_j)\Bigr]
--        = \sum_k \pi(T^{jk}n)\,\lambda_{kj}\varphi_k(n_k+1) \;+\; \pi(T^{j\to}n)\,\nu_j .$$
--      In words: from any state, the rate at which individuals leave colony $j$ equals the rate at
--      which they arrive into it.
--
--   2. *Boundary balance, equation (2.4).* For every state $n$,
--      $$\pi(n)\sum_k \nu_k = \sum_k \pi(T^{\to k}n)\,\mu_k\varphi_k(n_k+1).$$
--      In words: the rate at which individuals enter the system equals the rate at which they
--      leave it.
--
--   Summing the first family over $j$ and adding the second gives the equilibrium equations, which
--   is how Theorem 2.8 is proved. Each family is in fact equivalent to the traffic equations: (2.3)
--   reduces to equation (2.2) for the colony $j$, and (2.4) to the sum of (2.2) over all colonies,
--   namely $\sum_k \nu_k = \sum_k \alpha_k\mu_k$. Partial balance is strictly weaker than detailed
--   balance and strictly stronger than full balance.
--
--   **Formalization Note** The restriction $n_j \ge 1$ in the first family is the book's implicit
--   requirement that $T^{j\to}n$ and $T^{jk}n$ be states of $\mathbb{Z}_+^J$; without it, the
--   truncated natural subtraction used for occupancy counts would make the displayed equation
--   assert something the book does not. The term $k = j$ contributes nothing, since
--   $\lambda_{jj} = 0$.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 31-32 (PDF pp. 39-40), the partial balance equations (2.3) and (2.4) in the proof of Theorem 2.8: 'which will be satisfied if we can solve the partial balance equations, pi(n)[sum_k q(n, T^{jk}n) + q(n, T^{j->}n)] = sum_k pi(T^{jk}n) q(T^{jk}n, n) + pi(T^{j->}n) q(T^{j->}n, n)  (2.3)  and  pi(n) sum_k q(n, T^{->k}n) = sum_k pi(T^{->k}n) q(T^{->k}n, n)  (2.4).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyStochasticNetworks

theorem open_migration_partial_balance {J : ℕ} (lam : Fin J → Fin J → ℝ)
    (mu nu α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (hlamdiag : ∀ j, lam j j = 0)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hα : ∀ j, 0 < α j) (hg : ∀ j, 0 < g j)
    (htraffic : OpenTraffic lam mu nu α) :
    (∀ (n : Fin J → ℕ) (j : Fin J), 1 ≤ n j →
        openMigrationPi α g φ n * ((∑ k, lam j k * φ j (n j)) + mu j * φ j (n j))
          = (∑ k, openMigrationPi α g φ (Tjk j k n) * (lam k j * φ k (n k + 1)))
            + openMigrationPi α g φ (Tout j n) * nu j)
      ∧ (∀ n : Fin J → ℕ,
        openMigrationPi α g φ n * (∑ k, nu k)
          = ∑ k, openMigrationPi α g φ (Tin k n) * (mu k * φ k (n k + 1))) := by sorry

end KellyStochasticNetworks
