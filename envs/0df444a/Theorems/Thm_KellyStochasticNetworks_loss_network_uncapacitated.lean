-- Prove2me | Theorems.Thm_KellyStochasticNetworks_loss_network_uncapacitated
-- name    : KellyStochasticNetworks.loss_network_uncapacitated
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:42:52.93491+00:00
-- url     : https://prove2.me/theorems/f321f561-6b9f-49e7-b1d9-2a395bb40bdb
-- title:
--   The uncapacitated loss network: independent Poisson equilibrium
-- statement:
--   Consider a loss network with fixed routing in which every link has infinite capacity,
--   $C_1 = \dots = C_J = \infty$. Arriving calls are then never blocked: a call on route $r$
--   simply arrives at rate $\nu_r$, stays for an exponentially distributed time of unit mean, and
--   leaves. The state $n = (n_r)$ is a **linear migration process** with transition rates
--   $$q(n, T^{\to r}n) = \nu_r, \qquad q(n, T^{r\to}n) = n_r,$$
--   that is, the open migration process of Chapter 2 with $\lambda \equiv 0$, $\mu \equiv 1$ and
--   $\varphi_r(m) = m$.
--
--   Its equilibrium distribution is a product of independent Poisson distributions,
--   $$\pi(n) = \prod_{r}e^{-\nu_r}\frac{\nu_r^{\,n_r}}{n_r!},$$
--   and the process is in fact reversible. Concretely, for $\nu_r > 0$ this $\pi$ satisfies the
--   equilibrium equations for those rates, sums to $1$ over $\mathbb{Z}_+^{R}$, and satisfies the
--   detailed balance equations.
--
--   Because the capacities are infinite the individual routes are independent, which is what makes
--   the product form here elementary. Reversibility is the extra ingredient: it is what lets
--   Lemma 3.4 be applied to the truncation of this process to the feasible set of a network with
--   finite capacities, producing the exact equilibrium distribution (3.3).
--
--   **Formalization Note** The rates are written as the open migration rates published in mission
--   II of this series, instantiated at $\lambda \equiv 0$, $\mu \equiv 1$, $\varphi_r(m) = m$, so
--   the claim is literally that this loss network is that migration process. The traffic equations
--   (2.2) are then solved by $\alpha_r = \nu_r$, and $g_r = e^{\nu_r}$, so the first two conclusions
--   are an instance of the product-form theorem of mission II; the third, detailed balance, is not
--   and has to be checked directly.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 53 (PDF p. 61): 'Consider a loss network with fixed routing for which C_1 = ... = C_J = infinity. ... This system is described by a linear migration process with transition rates q(n, T^{->r}n) = nu_r, q(n, T^{r->}n) = n_r, and equilibrium distribution prod_{r in R} e^{-nu_r} nu_r^{n_r}/n_r!, n in Z^R. (Since the capacities are infinite, the individual routes become independent.)' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyStochasticNetworks

theorem loss_network_uncapacitated {R : ℕ} (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r) :
    FullBalance
        (fun n : Fin R → ℕ => ∏ r, Real.exp (-ν r) * (ν r ^ n r / (Nat.factorial (n r) : ℝ)))
        (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ)))
      ∧ HasSum
        (fun n : Fin R → ℕ => ∏ r, Real.exp (-ν r) * (ν r ^ n r / (Nat.factorial (n r) : ℝ))) 1
      ∧ DetailedBalance
        (fun n : Fin R → ℕ => ∏ r, Real.exp (-ν r) * (ν r ^ n r / (Nat.factorial (n r) : ℝ)))
        (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ))) := by sorry

end KellyStochasticNetworks
