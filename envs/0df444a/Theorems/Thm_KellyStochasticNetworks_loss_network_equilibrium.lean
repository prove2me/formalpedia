-- Prove2me | Theorems.Thm_KellyStochasticNetworks_loss_network_equilibrium
-- name    : KellyStochasticNetworks.loss_network_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:43:30.349259+00:00
-- url     : https://prove2.me/theorems/ea5a7c9c-b929-42fa-9387-04b37b826218
-- title:
--   Equation (3.3) — the exact equilibrium distribution of a loss network
-- statement:
--   A **loss network with fixed routing** has $J$ links, link $j$ carrying $C_j$ circuits, and $R$
--   routes; a call on route $r$ requires $A_{jr}$ circuits from link $j$ and is lost if any link
--   has fewer free. Calls on route $r$ arrive as a Poisson process of rate $\nu_r > 0$ and hold
--   their circuits for an exponentially distributed time of unit mean. The feasible states are
--   $S(C) = \{n \in \mathbb{Z}_+^R : An \le C\}$.
--
--   The process is the uncapacitated network — independent Poisson streams — truncated to $S(C)$,
--   so by Lemma 3.4 its equilibrium distribution is
--   $$\pi(n) = G(C)\prod_{r}\frac{\nu_r^{\,n_r}}{n_r!}, \qquad n \in S(C),
--     \qquad G(C) = \Bigl(\sum_{n \in S(C)}\prod_r \frac{\nu_r^{\,n_r}}{n_r!}\Bigr)^{-1},$$
--   equation (3.3). Precisely: $\pi$ satisfies the detailed balance equations for the truncated
--   rates, and sums to $1$ over $S(C)$.
--
--   In words, the equilibrium law of a loss network is that of independent Poisson random variables
--   conditioned on the linear inequalities $An \le C$. This is exact, not an approximation. It is
--   also not directly useful for a large or complex network: computing $G(C)$ is a sum over the
--   feasible states, and for a general non-negative integer matrix $A$ it is NP-hard, which is why
--   the rest of the chapter develops the Erlang fixed point approximation.
--
--   **Formalization Note** The truncated process lives on the subtype of feasible states, so a
--   transition that would leave $S(C)$ has no target and is suppressed automatically. Following the
--   book, $G(C)$ is the reciprocal of the sum of the weights, so the summability hypothesis is
--   stated for $G^{-1}$; it asserts convergence and the value at once.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 53 (PDF p. 61), equation (3.3): 'If we now truncate n to S(C) = {n : An <= C}, we obtain precisely the original loss network with fixed routing (and finite capacities). Therefore, its equilibrium distribution is pi(n) = G(C) prod_r nu_r^{n_r}/n_r!, n in S(C) = {n : An <= C}, with G(C) = (sum_{n in S(C)} prod_r nu_r^{n_r}/n_r!)^{-1}.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyStochasticNetworks

theorem loss_network_equilibrium {J R : ℕ} (A : Fin J → Fin R → ℕ) (C : Fin J → ℕ)
    (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r) (G : ℝ) (hG0 : G ≠ 0)
    (hG : HasSum (fun n : lossStates A C => lossWeight ν (n : Fin R → ℕ)) G⁻¹) :
    DetailedBalance (fun n : lossStates A C => G * lossWeight ν (n : Fin R → ℕ))
        (truncatedRates
          (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ)))
          (lossStates A C))
      ∧ HasSum (fun n : lossStates A C => G * lossWeight ν (n : Fin R → ℕ)) 1 := by sorry

end KellyStochasticNetworks
