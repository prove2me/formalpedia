-- Prove2me | Theorems.Thm_KellyStochasticNetworks_family_size_traffic
-- name    : KellyStochasticNetworks.family_size_traffic
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:28:58.600008+00:00
-- url     : https://prove2.me/theorems/f6bbea28-f685-409d-b32a-00236e34ab05
-- title:
--   The family-size process: traffic equations and the mean number of families
-- statement:
--   Kendall's **family-size process** is an open migration process with infinitely many colonies:
--   colony $j$ holds the families of size $j$, and $n_j$ is the number of such families. An
--   immigrant founds a new family of size $1$ at rate $\nu$; within a family of size $j$ each
--   individual gives birth at rate $\lambda$ and dies at rate $\mu$, so a family moves from colony
--   $j$ to colony $j+1$ at rate $j\lambda$ and to colony $j-1$ at rate $j\mu$; a family of size $1$
--   that loses its member becomes extinct and leaves the system at rate $\mu$. In migration
--   notation this is $\varphi_j(n_j) = n_j$ with $\lambda_{j,j+1} = j\lambda$,
--   $\lambda_{j,j-1} = j\mu$ for $j \ge 2$, $\nu_1 = \nu$ and $\mu_1 = \mu$.
--
--   Let $0 < \lambda < \mu$ and $\nu > 0$, and set
--   $$\alpha_j = \frac{\nu}{\lambda j}\left(\frac{\lambda}{\mu}\right)^{j}, \qquad j \ge 1 .$$
--   Then three things hold.
--
--   1. The traffic equation at colony $1$: $\alpha_1(\mu + \lambda) = \nu + 2\mu\,\alpha_2$.
--   2. The traffic equation at each colony $j \ge 2$:
--      $$\alpha_j\bigl(j\lambda + j\mu\bigr) = \alpha_{j-1}(j-1)\lambda + \alpha_{j+1}(j+1)\mu .$$
--   3. The series $\sum_{j \ge 1}\alpha_j$ converges, with
--      $$\sum_{j\ge 1}\alpha_j = -\frac{\nu}{\lambda}\log\!\left(1 - \frac{\lambda}{\mu}\right).$$
--
--   Because $\varphi_j(n) = n$ gives $g_j = e^{\alpha_j}$, the equilibrium numbers of families of
--   each size are independent Poisson variables of means $\alpha_j$, so the third identity is the
--   mean of the total number of distinct families. The condition $\lambda < \mu$ is the stability
--   condition, and it is exactly what makes the series converge.
--
--   **Formalization Note** Colonies are indexed by the positive integers, so the statements are
--   written at $j+1$, $j+2$ and $j+3$ to keep every index positive and avoid truncated
--   subtraction. Convergence of the series and the value of its sum are asserted together.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 34 (PDF p. 42), the family-size process of Kendall (1975): rates q(n, T^{j,j+1}n) = j lambda n_j, q(n, T^{j,j-1}n) = j mu n_j, q(n, T^{->1}n) = nu, q(n, T^{1->}n) = mu n_1. 'The traffic equations have a solution (check!) alpha_j = nu/(lambda j) (lambda/mu)^j' and 'the total number of distinct families, N = sum_j n_j, has a Poisson distribution with mean sum_j alpha_j = -(nu/lambda) log(1 - lambda/mu), from the series expansion of log(1-x).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyStochasticNetworks

theorem family_size_traffic (lam mu nu : ℝ) (hlam : 0 < lam) (hmu : lam < mu) (hnu : 0 < nu)
    (α : ℕ → ℝ)
    (hα : ∀ j : ℕ, α (j + 1) = nu / (lam * ((j : ℝ) + 1)) * (lam / mu) ^ (j + 1)) :
    α 1 * (mu + lam) = nu + α 2 * (2 * mu)
      ∧ (∀ i : ℕ, α (i + 2) * (((i : ℝ) + 2) * lam + ((i : ℝ) + 2) * mu)
            = α (i + 1) * (((i : ℝ) + 1) * lam) + α (i + 3) * (((i : ℝ) + 3) * mu))
      ∧ HasSum (fun j : ℕ => α (j + 1)) (-(nu / lam) * Real.log (1 - lam / mu)) := by sorry

end KellyStochasticNetworks
