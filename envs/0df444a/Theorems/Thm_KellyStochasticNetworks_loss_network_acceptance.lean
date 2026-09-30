-- Prove2me | Theorems.Thm_KellyStochasticNetworks_loss_network_acceptance
-- name    : KellyStochasticNetworks.loss_network_acceptance
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:43:58.703891+00:00
-- url     : https://prove2.me/theorems/58a01dee-dbb7-4361-818c-9d8bf3722997
-- title:
--   The acceptance probability $1 - L_r = G(C)/G(C - Ae_r)$
-- statement:
--   In a loss network with fixed routing, an arriving call on route $r$ is accepted exactly when
--   the current state $n$ leaves room for it, that is when $An + Ae_r \le C$, or equivalently
--   $n \in S(C - Ae_r)$, where $Ae_r$ is the $r$-th column of the incidence matrix. Since arrivals
--   are Poisson, they see time averages, so the equilibrium acceptance probability on route $r$ is
--   $$1 - L_r = \sum_{n \in S(C - Ae_r)}\pi(n) = \frac{G(C)}{G(C - Ae_r)} .$$
--
--   What is asserted here is the identity itself: with $\pi(n) = G(C)\prod_r \nu_r^{n_r}/n_r!$ the
--   equilibrium distribution of equation (3.3), and $G(C)$ and $G(C - Ae_r)$ the normalizing
--   constants of the two feasible sets, the sum of $\pi$ over $S(C - Ae_r)$ converges to
--   $G(C)/G(C - Ae_r)$.
--
--   The identity is the practical output of the exact theory: it turns blocking on a route into a
--   ratio of two normalizing constants. It is also what makes the exact theory impractical, since
--   both constants are sums over feasible sets.
--
--   **Formalization Note** The reduced capacity vector $C - Ae_r$ uses truncated natural
--   subtraction, and the hypothesis $A_{jr} \le C_j$ for every link makes that subtraction the
--   intended one; without it the route could not be carried even by an empty network. The
--   probabilistic step — that Poisson arrivals see time averages — is not part of this statement,
--   which is the identity between the sum and the ratio of normalizing constants.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 54 (PDF p. 62): 'Further, the equilibrium probability that a call on route r will be accepted is 1 - L_r = sum_{n in S(C - A e_r)} pi(n) = G(C)/G(C - A e_r), where e_r in S(C) is the unit vector that describes one call in progress on route r.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyStochasticNetworks

theorem loss_network_acceptance {J R : ℕ} (A : Fin J → Fin R → ℕ) (C : Fin J → ℕ)
    (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r) (r : Fin R) (hCr : ∀ j, A j r ≤ C j)
    (G GR : ℝ) (hG0 : G ≠ 0) (hGR0 : GR ≠ 0)
    (hG : HasSum (fun n : lossStates A C => lossWeight ν (n : Fin R → ℕ)) G⁻¹)
    (hGR : HasSum (fun n : lossStates A (fun j => C j - A j r) =>
              lossWeight ν (n : Fin R → ℕ)) GR⁻¹) :
    HasSum (fun n : lossStates A (fun j => C j - A j r) => G * lossWeight ν (n : Fin R → ℕ))
      (G / GR) := by sorry

end KellyStochasticNetworks
