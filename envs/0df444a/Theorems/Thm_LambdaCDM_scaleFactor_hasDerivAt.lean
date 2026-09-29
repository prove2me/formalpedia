-- Prove2me | Theorems.Thm_LambdaCDM_scaleFactor_hasDerivAt
-- name    : LambdaCDM.scaleFactor_hasDerivAt
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T02:49:31.540987+00:00
-- url     : https://prove2.me/theorems/a702212c-62d5-46ab-81ca-4b45890d3fa1
-- title:
--   Derivative of the ΛCDM scale factor: $\dot a = a H_0\sqrt{\Omega_\Lambda}\coth\theta$
-- statement:
--   Let $P$ record the parameters $H_0>0$, $\Omega_m>0$, $\Omega_\Lambda>0$ of a spatially flat ΛCDM model, so $\Omega_m+\Omega_\Lambda=1$, and put
--   $$\theta(t)=\tfrac32\sqrt{\Omega_\Lambda}\,H_0\,t,\qquad a(t)=\left(\frac{\Omega_m}{\Omega_\Lambda}\right)^{1/3}\sinh^{2/3}\theta(t).$$
--   For every time $t>0$ the scale factor is differentiable at $t$ with
--   $$\dot a(t)=a(t)\,H_0\sqrt{\Omega_\Lambda}\,\frac{\cosh\theta(t)}{\sinh\theta(t)} = a(t)\,H_0\sqrt{\Omega_\Lambda}\coth\theta(t).$$
--   Nothing is asserted for $t\le 0$, where $\sinh\theta(t)\le 0$ and the real power $x\mapsto x^{2/3}$ is not the intended branch.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib
import Definitions.Def_FlatLambdaCDM

namespace LambdaCDM

theorem scaleFactor_hasDerivAt (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (scaleFactor P)
      (scaleFactor P t * (P.H0 * Real.sqrt P.OL *
        (Real.cosh (theta P t) / Real.sinh (theta P t)))) t := by sorry

end LambdaCDM
