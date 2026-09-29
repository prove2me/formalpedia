-- Prove2me | Theorems.Thm_LambdaCDM_friedmann_equation
-- name    : LambdaCDM.friedmann_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T02:50:29.985059+00:00
-- url     : https://prove2.me/theorems/7de6260f-fa98-450b-a5d9-3766e1e7f9f1
-- title:
--   Friedmann equation $(\dot a/a)^2=H_0^2(\Omega_m a^{-3}+\Omega_\Lambda)$ for the closed form
-- statement:
--   With the flat ΛCDM parameters $H_0>0$, $\Omega_m>0$, $\Omega_\Lambda>0$, $\Omega_m+\Omega_\Lambda=1$, and
--   $$a(t)=\left(\frac{\Omega_m}{\Omega_\Lambda}\right)^{1/3}\sinh^{2/3}\!\left(\tfrac32\sqrt{\Omega_\Lambda}H_0t\right),$$
--   the closed form satisfies the first Friedmann equation of the radiation-free flat model at every time $t>0$:
--   $$\left(\frac{\dot a(t)}{a(t)}\right)^{2}=H_0^{2}\left(\frac{\Omega_m}{a(t)^{3}}+\Omega_\Lambda\right).$$
--   Here $\dot a$ is the derivative of $a$ and $a(t)^3$ is the third power; the statement is made only for $t>0$.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib
import Definitions.Def_FlatLambdaCDM

namespace LambdaCDM

theorem friedmann_equation (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    (deriv (scaleFactor P) t / scaleFactor P t) ^ 2
      = P.H0 ^ 2 * (P.Om / scaleFactor P t ^ 3 + P.OL) := by sorry

end LambdaCDM
