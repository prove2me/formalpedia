-- Prove2me | Theorems.Thm_LambdaCDM_lcdm_expansion_law
-- name    : LambdaCDM.lcdm_expansion_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:02:48.867728+00:00
-- url     : https://prove2.me/theorems/9babeaaf-8fc2-4b32-acaa-d0e39188b3e7
-- title:
--   The ΛCDM expansion law: closed-form solution of the flat Friedmann equation and the age $t_0$
-- statement:
--   Consider the minimal spatially flat, radiation-free ΛCDM model with present-day Hubble constant $H_0>0$ and density parameters $\Omega_m>0$, $\Omega_\Lambda>0$ satisfying $\Omega_m+\Omega_\Lambda=1$, and set
--   $$a(t)=\left(\frac{\Omega_m}{\Omega_\Lambda}\right)^{1/3}\sinh^{2/3}\!\left(\tfrac32\sqrt{\Omega_\Lambda}H_0t\right),\qquad t_0=\frac{2}{3H_0\sqrt{\Omega_\Lambda}}\operatorname{arsinh}\sqrt{\frac{\Omega_\Lambda}{\Omega_m}}.$$
--   Then all of the following hold.
--
--   1. **Positivity.** $a(t)>0$ for every $t>0$.
--   2. **Friedmann equation.** For every $t>0$,
--   $$\left(\frac{\dot a(t)}{a(t)}\right)^{2}=H_0^{2}\left(\frac{\Omega_m}{a(t)^{3}}+\Omega_\Lambda\right).$$
--   3. **The age is positive.** $t_0>0$.
--   4. **Normalization.** $a(t_0)=1$.
--
--   That is: the displayed formula is a positive solution of the flat matter-plus-$\Lambda$ Friedmann equation on the whole half-line $t>0$, and it is normalized to unity at the time $t_0$, which is therefore the model's predicted age of the universe. No claim is made about times $t\le 0$, and uniqueness of the solution is not asserted.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib
import Definitions.Def_FlatLambdaCDM

namespace LambdaCDM

theorem lcdm_expansion_law (P : FlatLCDM) :
    (∀ t : ℝ, 0 < t → 0 < scaleFactor P t) ∧
    (∀ t : ℝ, 0 < t →
      (deriv (scaleFactor P) t / scaleFactor P t) ^ 2
        = P.H0 ^ 2 * (P.Om / scaleFactor P t ^ 3 + P.OL)) ∧
    0 < age P ∧ scaleFactor P (age P) = 1 := by sorry

end LambdaCDM
