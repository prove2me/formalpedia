-- Prove2me | Theorems.Thm_LambdaCDM_accel_zero_iff
-- name    : LambdaCDM.accel_zero_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T02:59:35.434107+00:00
-- url     : https://prove2.me/theorems/bc5ab6a3-e5ae-4fee-8f6b-6cf31247dab9
-- title:
--   Deceleration-to-acceleration transition: $\ddot a=0 \iff a^3=\Omega_m/(2\Omega_\Lambda)$
-- statement:
--   With the flat ΛCDM closed form $a(t)=(\Omega_m/\Omega_\Lambda)^{1/3}\sinh^{2/3}(\tfrac32\sqrt{\Omega_\Lambda}H_0t)$, and for every time $t>0$, the second derivative of the scale factor vanishes exactly when the scale factor has reached the transition value:
--   $$\ddot a(t)=0\iff a(t)^{3}=\frac{\Omega_m}{2\Omega_\Lambda}.$$
--   Equivalently, the transition happens at redshift $1+z=1/a=(2\Omega_\Lambda/\Omega_m)^{1/3}$. The equivalence is asserted as a two-way implication at each individual $t>0$; the second derivative is the derivative of the derivative function.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib
import Definitions.Def_FlatLambdaCDM

namespace LambdaCDM

theorem accel_zero_iff (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    deriv (deriv (scaleFactor P)) t = 0 ↔ scaleFactor P t ^ 3 = P.Om / (2 * P.OL) := by sorry

end LambdaCDM
