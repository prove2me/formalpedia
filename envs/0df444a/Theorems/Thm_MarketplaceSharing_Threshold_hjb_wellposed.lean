-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_hjb_wellposed
-- name    : MarketplaceSharing.Threshold.hjb_wellposed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:22.67998+00:00
-- url     : https://prove2.me/theorems/bf857d38-0bdd-424a-ae8a-7a11be16f623
-- title:
--   §3.2, eq. (3), p. 8 — the HJB system (3) with Vₙ(0) = 0 has a unique solution
-- statement:
--   Fix parameters $(\pi, \theta, \lambda_D, \lambda_P, r)$ of the inventory sharing model, with $\theta\in[0,1]$, $\pi, \lambda_D, \lambda_P > 0$ and $r \ge 0$. Consider the HJB system (3): $V_0(t) = 0$ for $t \ge 0$, $V_n(0) = 0$ for all $n$, and for every $n \ge 1$ and $t \ge 0$
--   $$\frac{dV_n}{dt}(t) = \max_{z\in\{0,1\}}\Bigl[\bigl(\pi\lambda_D + z(1-\theta)\pi\lambda_P\bigr) - (\lambda_D + z\lambda_P)\bigl(V_n(t) - V_{n-1}(t)\bigr) - rV_n(t)\Bigr].$$
--
--   Then:
--   1. a family $(V_n)_{n\ge 0}$ solving this system on $[0,\infty)$ exists;
--   2. any two solutions agree at every $n$ and every $t \ge 0$.
--
--   The paper speaks of "the" revenue-to-go solving (3) and uses its existence throughout; this statement makes that premise explicit and guarantees that the hypothesis "$V$ is a revenue-to-go" carried by every other theorem of the mission can be met and determines $V$ on $[0, \infty)$.
--
--   **Formalization Note.** The derivative at $t = 0$ is one-sided (within $[0,\infty)$); nothing is asserted about $t < 0$, where solutions may differ.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), p. 8, §3.2, eq. (3); Appendix, p. 28 ("since Vn is the solution to the HJB equation")

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem hjb_wellposed (p : Params) :
    (∃ V : ℕ → ℝ → ℝ, p.IsRevenueToGo V) ∧
    ∀ V W : ℕ → ℝ → ℝ, p.IsRevenueToGo V → p.IsRevenueToGo W →
      ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → V n t = W n t := by sorry
end MarketplaceSharing.Threshold
