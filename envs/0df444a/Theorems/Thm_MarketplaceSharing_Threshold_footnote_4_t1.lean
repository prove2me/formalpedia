-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_footnote_4_t1
-- name    : MarketplaceSharing.Threshold.footnote_4_t1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:26.100664+00:00
-- url     : https://prove2.me/theorems/adfcbb5b-dcb3-46e6-8a18-d020ec5725e8
-- title:
--   Proof of Theorem 1, p. 30 (footnote 4) — with r = 0, t₁ = (1/λ)(ln(λ − θλP) − ln(θλD)); the printed formula is exact only at r = 0
-- statement:
--   In the inventory sharing model without discounting ($r = 0$) and with a positive commission $\theta > 0$, let $(V_n)$ be the revenue-to-go (a solution of the HJB system (3) with $V_0 \equiv 0$ and $V_n(0) = 0$) and let $t_1 = \sup\{t \ge 0 : V_1(t) \le (1-\theta)\pi\}$ be the sharing threshold of the last unit. With $\lambda = \lambda_D + \lambda_P$,
--   $$t_1 = \frac{1}{\lambda}\Bigl(\ln(\lambda - \theta\lambda_P) - \ln(\theta\lambda_D)\Bigr).$$
--
--   In particular $t_1$ is finite, and it is the explicit starting point of the recursive computation of the thresholds. In the base case of §3.3 ($\lambda_D = 0.2$, $\lambda_P = 0.8$, $\theta = 0.4$) it gives $t_1 = \ln 8.5 \approx 2.14$ months.
--
--   **Formalization Note.** The paper prints $t_1 = \frac{1}{\lambda+r}\bigl(\ln((\lambda+r) - \theta\lambda_P) - \ln(\theta\lambda_D)\bigr)$ for general $r$; that formula is correct only at $r = 0$ (for $r > 0$ the threshold is $\frac{1}{\lambda+r}\ln\frac{\lambda_D + (1-\theta)\lambda_P}{\theta\lambda_D - (1-\theta)r}$ when $\theta\lambda_D > (1-\theta)r$ and $\infty$ otherwise), so the statement carries $r = 0$. $\theta > 0$ keeps $\ln(\theta\lambda_D)$ finite; both logarithms have positive arguments.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), Appendix, proof of Theorem 1, p. 30, footnote 4

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem footnote_4_t1 (p : Params) (hr : p.r = 0) (hθ : 0 < p.θ) (V : ℕ → ℝ → ℝ)
    (hV : p.IsRevenueToGo V) :
    p.threshold V 1 = ((1 / (p.lamD + p.lamP) *
      (Real.log (p.lamD + p.lamP - p.θ * p.lamP) - Real.log (p.θ * p.lamD)) : ℝ) : EReal) := by sorry
end MarketplaceSharing.Threshold
