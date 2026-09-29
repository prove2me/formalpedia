-- Prove2me | Theorems.Thm_LambdaCDM_scaleFactor_strictMonoOn_and_tendsto_zero
-- name    : LambdaCDM.scaleFactor_strictMonoOn_and_tendsto_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:00:27.074504+00:00
-- url     : https://prove2.me/theorems/8c7731d4-7cce-477a-80aa-f89fd0def507
-- title:
--   Big-bang limit and monotone expansion of the ΛCDM scale factor
-- statement:
--   For flat ΛCDM parameters, the closed-form scale factor $a$ is strictly increasing on the open half-line $t>0$: if $0<s<t$ then $a(s)<a(t)$. Moreover $a(t)\to 0$ as $t\downarrow 0$ through positive times.
--
--   Together these say that the model expands monotonically and that the big bang sits at $t=0$: the scale factor has limit zero there, so $t=0$ is the initial singularity of the closed form. No claim is made about $t\le 0$.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib
import Definitions.Def_FlatLambdaCDM

namespace LambdaCDM

theorem scaleFactor_strictMonoOn_and_tendsto_zero (P : FlatLCDM) :
    StrictMonoOn (scaleFactor P) (Set.Ioi 0) ∧
      Filter.Tendsto (scaleFactor P) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by sorry

end LambdaCDM
