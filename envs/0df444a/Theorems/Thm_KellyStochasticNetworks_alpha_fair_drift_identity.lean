-- Prove2me | Theorems.Thm_KellyStochasticNetworks_alpha_fair_drift_identity
-- name    : KellyStochasticNetworks.alpha_fair_drift_identity
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:51:03.523463+00:00
-- url     : https://prove2.me/theorems/2aad391b-8b9a-4dc3-a527-d481a80ee610
-- title:
--   Equation (8.3) — the drift of the Lyapunov function in terms of the loads
-- statement:
--   The Lyapunov function of Theorem 8.2 is
--   $$L(n) = \sum_r \frac{w_r}{\mu_r}\,\rho_r^{-\alpha}\,\frac{n_r^{\alpha+1}}{\alpha+1},$$
--   whose partial derivative in $n_r$ is $(w_r/\mu_r)\rho_r^{-\alpha}n_r^{\alpha}$. Since the flow
--   count on route $r$ has drift $\nu_r - \mu_r n_r x_r(n)$ — arrivals at rate $\nu_r$, departures at
--   rate $\mu_r n_r x_r(n)$ — the chain rule gives the drift of $L$ as
--   $$\sum_r \frac{w_r}{\mu_r}\,\rho_r^{-\alpha}\,n_r^{\alpha}\bigl(\nu_r - \mu_r n_r x_r(n)\bigr).$$
--
--   The identity to record is that this equals
--   $$\sum_r w_r\,\rho_r^{-\alpha}\,n_r^{\alpha}\bigl(\rho_r - n_r x_r(n)\bigr),$$
--   where $\rho_r = \nu_r/\mu_r$ is the load on route $r$. Dividing through by $\mu_r$ turns arrival
--   rates into loads and departure rates into the aggregate rate $X_r = n_r x_r$, which is what puts
--   the drift in the form the tangent-plane inequality can bound: the loads $\rho$ and the aggregate
--   rates $X$ are then two points of the same feasible region.
--
--   **Formalization Note** The identity is deterministic arithmetic, one summand at a time; the
--   approximation of the true drift by this expression, which the book flags as inexact for small
--   $n_r$, is not part of it. The load is introduced by its defining identity $\rho_r = \nu_r/\mu_r$
--   rather than substituted throughout, so the two sides read as the book writes them.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 190 (PDF p. 198), equation (8.3): '(1/delta t) E[L(n(t+delta t)) - L(n(t)) | n(t)] approx sum_{r in R} (partial L / partial n_r) . (1/delta t) E[n_r(t+delta t) - n_r(t) | n(t)] = sum_r (w_r/mu_r) rho_r^{-alpha} n_r^alpha ( nu_r - mu_r n_r x_r(n(t)) ) = sum_r w_r rho_r^{-alpha} n_r^alpha ( rho_r - n_r x_r(n(t)) ). (8.3)' The Lyapunov function L(n) = sum_r (w_r/mu_r) rho_r^{-alpha} n_r^{alpha+1}/(alpha+1) is on the same page. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_drift_identity {R : ℕ} (w n ν μ x : Fin R → ℝ) (α : ℝ)
    (hμ : ∀ r, 0 < μ r) (ρ : Fin R → ℝ) (hρ : ∀ r, ρ r = ν r / μ r) :
    (∑ r, (w r / μ r) * ρ r ^ (-α) * n r ^ α * (ν r - μ r * (n r * x r)))
      = ∑ r, w r * ρ r ^ (-α) * n r ^ α * (ρ r - n r * x r) := by sorry

end KellyStochasticNetworks
