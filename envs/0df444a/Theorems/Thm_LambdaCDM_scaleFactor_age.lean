-- Prove2me | Theorems.Thm_LambdaCDM_scaleFactor_age
-- name    : LambdaCDM.scaleFactor_age
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T02:54:00.457899+00:00
-- url     : https://prove2.me/theorems/c6254f51-ebfb-4d93-ba3a-f189c171d8b6
-- title:
--   Normalization $a(t_0)=1$ at the ΛCDM age $t_0$
-- statement:
--   For flat ΛCDM parameters $H_0>0$, $\Omega_m>0$, $\Omega_\Lambda>0$ with $\Omega_m+\Omega_\Lambda=1$, define the age
--   $$t_0=\frac{2}{3H_0\sqrt{\Omega_\Lambda}}\operatorname{arsinh}\sqrt{\frac{\Omega_\Lambda}{\Omega_m}}.$$
--   Then the closed-form scale factor takes the value one there:
--   $$a(t_0)=\left(\frac{\Omega_m}{\Omega_\Lambda}\right)^{1/3}\sinh^{2/3}\!\left(\tfrac32\sqrt{\Omega_\Lambda}H_0t_0\right)=1,$$
--   which is the normalization that identifies $t_0$ with the present epoch and hence with the predicted age of the universe.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib
import Definitions.Def_FlatLambdaCDM

namespace LambdaCDM

theorem scaleFactor_age (P : FlatLCDM) : scaleFactor P (age P) = 1 := by sorry

end LambdaCDM
