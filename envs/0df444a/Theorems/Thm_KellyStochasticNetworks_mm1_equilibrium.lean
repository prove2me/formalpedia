-- Prove2me | Theorems.Thm_KellyStochasticNetworks_mm1_equilibrium
-- name    : KellyStochasticNetworks.mm1_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:24:56.84206+00:00
-- url     : https://prove2.me/theorems/2a945dba-2668-4523-a19a-9d158f435b82
-- title:
--   The equilibrium distribution of an M/M/1 queue
-- statement:
--   An **M/M/1 queue** has a Poisson arrival stream of rate $\lambda$, a single server, and
--   independent exponential service times of parameter $\mu$. Writing $X(t)$ for the number of
--   customers present, including the one in service, $X$ is a Markov process on
--   $\{0, 1, 2, \dots\}$ with transition rates
--   $$q(j, j+1) = \lambda \quad (j \ge 0), \qquad q(j, j-1) = \mu \quad (j \ge 1).$$
--
--   Suppose $0 < \lambda < \mu$ and write $\rho = \lambda/\mu$ for the **traffic intensity**. Then
--   the geometric distribution
--   $$\pi(j) = (1-\rho)\rho^{\,j}, \qquad j = 0, 1, 2, \dots,$$
--   satisfies the detailed balance equations for these rates, and its terms sum to $1$. It is
--   therefore the equilibrium distribution of the queue, and the queue is reversible.
--
--   The two conclusions are stated together because either alone is weaker than the claim:
--   detailed balance is satisfied by every positive multiple of $\pi$, while summing to $1$ says
--   nothing about the dynamics.
--
--   **Formalization Note** The hypothesis $\lambda < \mu$ is exactly what makes the geometric
--   series converge, and it is the stability condition for the queue. Convergence and the value of
--   the sum are asserted together.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 22 (PDF p. 30), section 2.1: 'If the arrival rate lambda is less than the service rate mu, the distribution pi(j) = (1 - rho) rho^j, j = 0, 1, ..., satisfies the detailed balance equations (1.4) and is thus the equilibrium distribution, where rho = lambda/mu is the traffic intensity.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyStochasticNetworks

theorem mm1_equilibrium (lam mu : ℝ) (hlam : 0 < lam) (hmu : lam < mu) :
    DetailedBalance (fun j : ℕ => (1 - lam / mu) * (lam / mu) ^ j) (mm1Rates lam mu)
      ∧ HasSum (fun j : ℕ => (1 - lam / mu) * (lam / mu) ^ j) 1 := by sorry

end KellyStochasticNetworks
