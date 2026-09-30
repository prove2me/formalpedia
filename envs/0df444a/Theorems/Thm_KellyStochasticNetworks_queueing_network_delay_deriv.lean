-- Prove2me | Theorems.Thm_KellyStochasticNetworks_queueing_network_delay_deriv
-- name    : KellyStochasticNetworks.queueing_network_delay_deriv
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:01:02.405096+00:00
-- url     : https://prove2.me/theorems/3e27f91d-c376-4be3-ada0-cfa956bd626b
-- title:
--   Section 4.3.1 — the externality decomposition of $dW/d\nu_r$
-- statement:
--   Consider an open network of queues in which a route is a set of queues a customer must
--   traverse. Queue $j$ has service rate $\varphi_j$, customers on route $r$ arrive at rate
--   $\nu_r$, and the mean sojourn time at queue $j$ is $1/(\varphi_j - \lambda_j)$ with
--   $\lambda_j = \sum_{r' : j \in r'}\nu_{r'}$, which is the behaviour of a network of $\cdot$/M/1
--   queues. If a unit delay of a customer on route $r$ costs $w_r$, the mean cost per unit time is
--   $$W(\nu;\varphi) = \sum_r w_r \sum_{j \in r}\frac{\nu_r}{\varphi_j - \lambda_j}.$$
--
--   Suppose every queue is stable, $\lambda_j < \varphi_j$. Then $W$ is differentiable in the
--   arrival rate on route $r$, with
--   $$\frac{dW}{d\nu_r} \;=\; \sum_{j \in r}\left[\;
--     \underbrace{\frac{w_r}{\varphi_j - \lambda_j}}_{\text{delay the extra customer suffers at } j}
--     \;+\;
--     \underbrace{\sum_{r' : j \in r'}\frac{\nu_{r'}w_{r'}}{(\varphi_j - \lambda_j)^2}}_{\text{knock-on cost to everyone else through } j}
--     \;\right].$$
--
--   This is an exact derivative, not an approximation, and its two terms separate the private cost
--   from the **externality**: one extra customer on route $r$ is delayed at each queue on its
--   route, and it also delays every other customer passing through those queues. The
--   decomposition is what licenses shifting traffic towards routes with smaller derivatives, and it
--   is the same accounting that makes a marginal-cost toll align selfish routing with the social
--   optimum.
--
--   **Formalization Note** The derivative in $\nu_r$ is stated as an ordinary derivative of the
--   function obtained by varying the $r$-th coordinate of $\nu$ and holding the others fixed, so
--   no partial-derivative API is presupposed. Sums over the queues of a route are written as sums
--   over all queues weighted by the incidence matrix, whose entries are $0$ or $1$. The stability
--   hypothesis $\lambda_j < \varphi_j$ is what keeps every denominator away from zero.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 101 (PDF p. 109), section 4.3.1: 'dW/dnu_r = sum_{j in r} [ w_r/(phi_j - lambda_j) + sum_{r' : j in r'} nu_{r'} w_{r'}/(phi_j - lambda_j)^2 ], where the first term is the extra delay at queue j of another customer on route r and the second is the knock-on cost, or externality, to later customers on routes through j of another customer on route r. The expression gives the exact derivative.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem queueing_network_delay_deriv {J R : ℕ} (A : Fin J → Fin R → ℝ) (w ν : Fin R → ℝ)
    (φ : Fin J → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hstab : ∀ j, (∑ r', A j r' * ν r') < φ j) (r : Fin R) :
    HasDerivAt (fun t : ℝ => queueingCost A w (Function.update ν r t) φ)
      (∑ j, A j r * (w r / (φ j - ∑ r', A j r' * ν r')
        + ∑ r', A j r' * (ν r' * w r') / (φ j - ∑ r'', A j r'' * ν r'') ^ 2))
      (ν r) := by sorry

end KellyStochasticNetworks
