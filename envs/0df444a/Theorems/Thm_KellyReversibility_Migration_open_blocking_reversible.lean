-- Prove2me | Theorems.Thm_KellyReversibility_Migration_open_blocking_reversible
-- name    : KellyReversibility.Migration.open_blocking_reversible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:36:41.251616+00:00
-- url     : https://prove2.me/theorems/da4c2393-8cf7-4bd5-bc49-eb4c47efe885
-- title:
--   Theorem 6.2 — an open migration process with blocking is reversible; its equilibrium is the product form (6.3) with independent colonies
-- statement:
--   Consider an **open migration process with blocking** on $J$ colonies. The state is $n = (n_1,\dots,n_J) \in \mathbb{N}^J$, and the transition rates are
--   $$q(n, T_{jk}n) = \lambda_{jk}\varphi_j(n_j)\psi_k(n_k), \qquad q(n, T_{j\cdot}n) = \mu_j\varphi_j(n_j), \qquad q(n, T_{\cdot k}n) = \nu_k\psi_k(n_k),$$
--   equations (6.2), (6.5), (6.6): an individual moves from colony $j$ to colony $k$, leaves the system from colony $j$, or enters the system at colony $k$. Assume $\lambda_{jk}, \mu_j, \nu_k \ge 0$, $\lambda_{jj} = 0$, an individual can reach any colony from outside the system and leave the system from any colony (directly or via a chain of colonies), $\varphi_j(0) = 0$, $\varphi_j(n) > 0$ for $n > 0$ and $\psi_j(n) > 0$ for $n \ge 0$.
--
--   Suppose there are positive constants $\alpha_1,\dots,\alpha_J$ with
--   $$\alpha_j\lambda_{jk} = \alpha_k\lambda_{kj} \quad (6.4), \qquad \alpha_j\mu_j = \nu_j \quad (6.7),$$
--   and that the process is stationary, i.e. each colony series converges:
--   $$g_j = \sum_{m=0}^{\infty} \alpha_j^{m}\prod_{r=1}^{m}\frac{\psi_j(r-1)}{\varphi_j(r)} < \infty.$$
--   Let $B = \prod_j g_j^{-1}$ and
--   $$\pi(n) = B\prod_{j=1}^{J}\Bigl\{\alpha_j^{n_j}\prod_{r=1}^{n_j}\frac{\psi_j(r-1)}{\varphi_j(r)}\Bigr\}. \tag{6.3}$$
--   Then:
--
--   1. $\pi$ satisfies the detailed balance conditions $\pi(n)q(n,m) = \pi(m)q(m,n)$ for all states $n,m$;
--   2. $\pi$ satisfies the equilibrium equations $\pi(n)\sum_m q(n,m) = \sum_m \pi(m)q(m,n)$;
--   3. $\pi(n) > 0$ for every $n$, and $\sum_n \pi(n) = 1$;
--   4. in $\pi$ the colony counts $n_1,\dots,n_J$ are independent: with $\pi_j(m) = g_j^{-1}\alpha_j^{m}\prod_{r=1}^{m}\psi_j(r-1)/\varphi_j(r)$, each $\pi_j$ is a probability distribution on $\mathbb{N}$, the marginal of $\pi$ on colony $j$ is $\pi_j$, and $\pi(n) = \prod_j \pi_j(n_j)$.
--
--   So the open process is reversible, (6.3) is its equilibrium distribution, and in equilibrium the numbers in the colonies are independent, even though the rate of moving into a colony depends on how many are already there.
--
--   **Formalization Note** The statement is at the level of transition rates. "Reversible" is read as detailed balance of the equilibrium distribution for the rates; Theorem 1.3 of the book identifies this with reversibility of the stationary process, and this item does not construct the process. Stationarity is carried as the convergence of every colony series (`HasSum` to $g_j$), and the normalizing constant is fixed as $B = \prod_j g_j^{-1}$ rather than left free. Sums over the countable state space $\mathbb{N}^J$ are unconditional sums; the marginal on colony $j$ is the sum of $\pi$ over the states with $n_j = m$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 136–137, Theorem 6.2 (rates (6.2) p. 135, (6.5)–(6.6) p. 136; form (6.3), conditions (6.4), (6.7) p. 136)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyReversibility_Migration_BlockingRates

namespace KellyReversibility.Migration

open KellyStochasticNetworks

/-- **Theorem 6.2** (Kelly, *Reversibility and Stochastic Networks*, pp. 136–137).  For an open
migration process with transition rates (6.2), (6.5), (6.6) and positive constants `α_j`
satisfying (6.4) and (6.7), suppose each colony series
`∑_m α_j^m ∏_{r=1}^m ψ_j(r-1)/φ_j(r)` converges, to `g_j`.  Then
`π(n) = B ∏_j α_j^{n_j} ∏_{r=1}^{n_j} ψ_j(r-1)/φ_j(r)` with `B = ∏_j g_j⁻¹` is in detailed
balance with the rates, satisfies the equilibrium equations, is positive and sums to one; and in
`π` the colony counts are independent: for each colony `j` the marginal law of `n_j` is
`π_j(m) = g_j⁻¹ α_j^m ∏_{r=1}^m ψ_j(r-1)/φ_j(r)`, a probability distribution on `ℕ`, and `π` is the
product of these marginals. -/
theorem open_blocking_reversible {J : ℕ}
    (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ) (φ ψ : Fin J → ℕ → ℝ) (α g : Fin J → ℝ)
    (hlamdiag : ∀ j, lam j j = 0) (hlam : ∀ j k, 0 ≤ lam j k)
    (hmu : ∀ j, 0 ≤ mu j) (hnu : ∀ j, 0 ≤ nu j)
    (hconn : OpenConnected lam mu nu)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hψpos : ∀ j r, 0 < ψ j r)
    (hα : ∀ j, 0 < α j) (hbal : BlockingBalance lam α) (hout : ∀ j, α j * mu j = nu j)
    (hg : ∀ j, HasSum (fun m : ℕ => α j ^ m * psiPhiProd ψ φ j m) (g j)) :
    let B : ℝ := ∏ j, (g j)⁻¹
    let π : (Fin J → ℕ) → ℝ := fun n => B * blockingWeight α ψ φ n
    let πj : Fin J → ℕ → ℝ := fun j m => (g j)⁻¹ * (α j ^ m * psiPhiProd ψ φ j m)
    DetailedBalance π (openBlockingRates lam mu nu φ ψ)
      ∧ FullBalance π (openBlockingRates lam mu nu φ ψ)
      ∧ (∀ n, 0 < π n)
      ∧ HasSum π 1
      ∧ (∀ j, HasSum (πj j) 1)
      ∧ (∀ (j : Fin J) (m : ℕ), HasSum (fun n : {n : Fin J → ℕ // n j = m} => π n.1) (πj j m))
      ∧ (∀ n, π n = ∏ j, πj j (n j)) := by sorry

end KellyReversibility.Migration
