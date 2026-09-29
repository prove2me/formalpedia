-- Prove2me | Theorems.Thm_LambdaCDM_accel_pos_iff
-- name    : LambdaCDM.accel_pos_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:00:04.135591+00:00
-- url     : https://prove2.me/theorems/bb0a5d82-1fa1-4417-a820-7673d7a3d7ef
-- title:
--   Accelerating expansion criterion: $\ddot a>0 \iff \Omega_m<2\Omega_\Lambda a^3$
-- statement:
--   For the flat ΛCDM closed form and every time $t>0$, the expansion is accelerating at $t$ exactly when the scale factor has passed the transition value:
--   $$\ddot a(t)>0\iff \Omega_m<2\Omega_\Lambda\,a(t)^{3}.$$
--   Together with the monotonicity of $a$ this says that the model decelerates before the transition epoch and accelerates after it, with the strict inequality on both sides.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib
import Definitions.Def_FlatLambdaCDM

namespace LambdaCDM

theorem accel_pos_iff (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    0 < deriv (deriv (scaleFactor P)) t ↔ P.Om < 2 * P.OL * scaleFactor P t ^ 3 := by sorry

end LambdaCDM
