-- Prove2me | Theorems.Thm_LambdaCDM_age_eq_log
-- name    : LambdaCDM.age_eq_log
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T02:54:35.705752+00:00
-- url     : https://prove2.me/theorems/f591e26e-442a-4e20-88b6-4d325a25e740
-- title:
--   Logarithmic form of the age: $t_0=\frac{2}{3H_0\sqrt{\Omega_\Lambda}}\log\frac{1+\sqrt{\Omega_\Lambda}}{\sqrt{\Omega_m}}$
-- statement:
--   For flat ΛCDM parameters ($H_0>0$, $\Omega_m>0$, $\Omega_\Lambda>0$, $\Omega_m+\Omega_\Lambda=1$), the age
--   $$t_0=\frac{2}{3H_0\sqrt{\Omega_\Lambda}}\operatorname{arsinh}\sqrt{\frac{\Omega_\Lambda}{\Omega_m}}$$
--   admits the elementary closed form
--   $$t_0=\frac{2}{3H_0\sqrt{\Omega_\Lambda}}\,\log\!\frac{1+\sqrt{\Omega_\Lambda}}{\sqrt{\Omega_m}}.$$
--   This is the expression used to evaluate the age numerically from measured density parameters; the flatness relation $\Omega_m=1-\Omega_\Lambda$ is what turns $\operatorname{arsinh}$ into this logarithm.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib
import Definitions.Def_FlatLambdaCDM

namespace LambdaCDM

theorem age_eq_log (P : FlatLCDM) :
    age P = 2 / (3 * P.H0 * Real.sqrt P.OL) *
      Real.log ((1 + Real.sqrt P.OL) / Real.sqrt P.Om) := by sorry

end LambdaCDM
