-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_share_optimal_iff
-- name    : MarketplaceSharing.Threshold.share_optimal_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:18.413229+00:00
-- url     : https://prove2.me/theorems/c387991f-99c2-40c3-b7c7-802473264e77
-- title:
--   §3.2, p. 8 — sharing is optimal iff (1 − θ)π ≥ ΔVₙ(t)
-- statement:
--   In the inventory sharing model with $\lambda_P > 0$, let $(V_n)$ be any family of functions of the time-to-go, $n$ a number of units and $t$ a time. Write $\Delta V_n(t) = V_n(t) - V_{n-1}(t)$ and let
--   $$H_z = \bigl(\pi\lambda_D + z(1-\theta)\pi\lambda_P\bigr) - (\lambda_D + z\lambda_P)\,\Delta V_n(t) - rV_n(t), \qquad z \in \{0,1\},$$
--   be the bracket of the HJB equation (3). Sharing ($z = 1$) attains $\max_z H_z$ if and only if
--   $$\Delta V_n(t) \le (1-\theta)\pi.$$
--
--   This is the paper's observation that sharing pays exactly when the platform margin of a sale covers the marginal value of the unit; it is the bridge between the HJB equation and the threshold $t_n$.
--
--   **Formalization Note.** The statement is pointwise algebra on the bracket and does not need $V$ to solve (3). It uses $\lambda_P > 0$ from the standing parameters.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), p. 8, §3.2, sentence after eq. (3)

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem share_optimal_iff (p : Params) (V : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) :
    p.IsOptimalDecision V n t true ↔ marginal V n t ≤ p.platformMargin := by sorry
end MarketplaceSharing.Threshold
