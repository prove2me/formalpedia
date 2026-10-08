-- Prove2me | Theorems.Thm_KellyReversibility_Migration_closed_blocking_reversible
-- name    : KellyReversibility.Migration.closed_blocking_reversible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:36:36.048274+00:00
-- url     : https://prove2.me/theorems/b8e71e28-3951-4665-b2ea-2b7b50a79a3c
-- title:
--   Theorem 6.1 — a closed migration process with blocking rates (6.2) is reversible with product-form equilibrium (6.3)
-- statement:
--   Consider a **closed migration process with blocking** on $J \ge 1$ colonies with $N$ individuals. Its state space is
--   $$\mathcal{S} = \Bigl\{ n \in \mathbb{N}^J : \sum_{j=1}^J n_j = N \Bigr\},$$
--   and its only transitions move one individual from colony $j$ to colony $k$, at rate $q(n, T_{jk}n) = \lambda_{jk}\varphi_j(n_j)\psi_k(n_k)$ (6.2). Assume $\lambda_{jk} \ge 0$, $\lambda_{jj} = 0$, the $\lambda_{jk}$ allow an individual to pass between any two colonies (directly or via a chain), $\varphi_j(0) = 0$, $\varphi_j(n) > 0$ for $n > 0$, and $\psi_j(n) > 0$ for $n \ge 0$.
--
--   Suppose there are positive constants $\alpha_1,\dots,\alpha_J$ with
--   $$\alpha_j\lambda_{jk} = \alpha_k\lambda_{kj} \qquad \text{for all } j,k. \tag{6.4}$$
--   Let $B$ be the normalizing constant
--   $$B^{-1} = \sum_{n \in \mathcal{S}} \prod_{j=1}^{J}\Bigl\{\alpha_j^{n_j}\prod_{r=1}^{n_j}\frac{\psi_j(r-1)}{\varphi_j(r)}\Bigr\},$$
--   and let $\pi(n) = B\prod_{j=1}^{J}\bigl\{\alpha_j^{n_j}\prod_{r=1}^{n_j}\psi_j(r-1)/\varphi_j(r)\bigr\}$ for $n \in \mathcal{S}$ (6.3), and $\pi(n) = 0$ for $n \notin \mathcal{S}$. Then:
--
--   1. $\pi$ satisfies the detailed balance conditions $\pi(n)q(n,m) = \pi(m)q(m,n)$ for all states $n, m$;
--   2. $\pi$ satisfies the equilibrium equations $\pi(n)\sum_m q(n,m) = \sum_m \pi(m)q(m,n)$;
--   3. $\pi(n) > 0$ for every $n \in \mathcal{S}$;
--   4. $\sum_n \pi(n) = 1$.
--
--   That is, (6.3) is the equilibrium distribution of the process, and the process is reversible. With $\psi_j \equiv 1$ this is the reversible case of Theorem 2.3; the point of the theorem is that a receiving-colony dependence $\psi_k(n_k)$ is compatible with a product-form equilibrium once the parameters satisfy (6.4).
--
--   **Formalization Note** The statement is at the level of transition rates. "Reversible" is read as detailed balance of the equilibrium distribution for the rates; Theorem 1.3 of the book identifies this with reversibility of the stationary process, and this item does not construct the process. The distribution is written on all of $\mathbb{N}^J$ and vanishes off $\mathcal{S}$; every transition preserves $\sum_j n_j$, so this is the same as working on $\mathcal{S}$. The constant $B$ is carried through the hypothesis that the (finite) sum of the weights over $\mathcal{S}$ equals $B^{-1}$. The hypothesis $J \ge 1$ makes $\mathcal{S}$ nonempty for every $N$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 136, Theorem 6.1 (rates (6.2) p. 135; form (6.3), condition (6.4) p. 136)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyReversibility_Migration_BlockingRates

namespace KellyReversibility.Migration

open KellyStochasticNetworks

/-- **Theorem 6.1** (Kelly, *Reversibility and Stochastic Networks*, p. 136).  For a closed
migration process with transition rates (6.2) and positive constants `α_j` satisfying (6.4), the
function `π(n) = B ∏_j α_j^{n_j} ∏_{r=1}^{n_j} ψ_j(r-1)/φ_j(r)` on
`𝒮 = {n : ∑_j n_j = N}` (and `0` off `𝒮`), with `B` the normalizing constant over `𝒮`, is in
detailed balance with the rates, satisfies the equilibrium equations, is positive on `𝒮` and
sums to one. -/
theorem closed_blocking_reversible {J : ℕ} (hJ : 0 < J) (N : ℕ)
    (lam : Fin J → Fin J → ℝ) (φ ψ : Fin J → ℕ → ℝ) (α : Fin J → ℝ) (B : ℝ)
    (hlamdiag : ∀ j, lam j j = 0) (hlam : ∀ j k, 0 ≤ lam j k)
    (hconn : ClosedConnected lam)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hψpos : ∀ j r, 0 < ψ j r)
    (hα : ∀ j, 0 < α j) (hbal : BlockingBalance lam α)
    (hB : HasSum (fun n : {n : Fin J → ℕ // ∑ j, n j = N} => blockingWeight α ψ φ n.1) B⁻¹) :
    let π : (Fin J → ℕ) → ℝ := fun n =>
      if ∑ j, n j = N then B * blockingWeight α ψ φ n else 0
    DetailedBalance π (closedBlockingRates lam φ ψ)
      ∧ FullBalance π (closedBlockingRates lam φ ψ)
      ∧ (∀ n : Fin J → ℕ, ∑ j, n j = N → 0 < π n)
      ∧ HasSum π 1 := by sorry

end KellyReversibility.Migration
