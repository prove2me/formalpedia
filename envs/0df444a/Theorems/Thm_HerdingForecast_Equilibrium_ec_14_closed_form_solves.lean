-- Prove2me | Theorems.Thm_HerdingForecast_Equilibrium_ec_14_closed_form_solves
-- name    : HerdingForecast.Equilibrium.ec_14_closed_form_solves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:04.037254+00:00
-- url     : https://prove2.me/theorems/0e8952cc-fed5-4838-b9f6-a18617320b1a
-- title:
--   (EC.14), p. ec42 (PDF 80) — the closed-form profile (10)–(11) is admissible and solves (EC.11)–(EC.12)
-- statement:
--   Assume $K \ge 2$, $\tau_x, \tau_y > 0$ and $0 \le r < 1$. The profile in which every expert $k$ reports
--   $$\mu_k = \mu^{MS}_k = \frac{(1-r)\tau_x}{(1-r)\tau_x+\tau_y}x_k + \frac{\tau_y}{(1-r)\tau_x+\tau_y}y,\qquad \sigma_k^2 = a(x_k-y)^2 + d,$$
--   with $a, d$ as in (11), is admissible, and at every signal pair $(x_k, y)$ its forecast equals the right-hand sides of the first-order conditions (EC.11)–(EC.12) computed against itself: $\mu_k = \mu^*$ and $\sigma_k^2 = v^*$.
--
--   Together with the best-response characterization (EC.11)–(EC.12), this shows that the closed-form profile is an equilibrium.
--
--   **Formalization Note** Admissibility includes positivity of $a(x-y)^2 + d$ and integrability of the reported means, squared means, variances and log-variances under the predictive law, each a proof obligation here.
-- source:
--   Jia, Keppo & Satopää, Herding in Probabilistic Forecasts, SSRN 3674961 (PDF sha256 820fb50d…), p. ec42 (PDF 80), (EC.14); pp. ec41–ec42, (EC.11)–(EC.13)

import Mathlib
import Definitions.Def_HerdingForecast_Equilibrium_Model

namespace HerdingForecast.Equilibrium
theorem ec_14_closed_form_solves (P : Params) (hP : Standing P) :
    Admissible P (closedForm P) ∧
      ∀ (k : Fin P.K) (x y : ℝ),
        closedForm P k x y = (brMean P (closedForm P) k x y, brVar P (closedForm P) k x y) := by sorry
end HerdingForecast.Equilibrium
