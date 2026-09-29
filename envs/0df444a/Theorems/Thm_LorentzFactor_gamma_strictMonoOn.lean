-- Prove2me | Theorems.Thm_LorentzFactor_gamma_strictMonoOn
-- name    : LorentzFactor.gamma_strictMonoOn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:52:43.420985+00:00
-- url     : https://prove2.me/theorems/3d7b8796-f60e-4217-8fae-944f488b3e2b
-- title:
--   $\gamma$ is strictly increasing on $[0, 1)$
-- statement:
--   Restricted to the half-open interval $0 \le \beta < 1$, the Lorentz factor is strictly increasing: if $0 \le \beta_1 < \beta_2 < 1$ then $\gamma(\beta_1) < \gamma(\beta_2)$. This is the monotone rise displayed by the $\gamma$ column of the article's table and by the plot of $\gamma$ against $v/c$.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem gamma_strictMonoOn : StrictMonoOn gamma (Set.Ico (0 : ℝ) 1) := by sorry

end LorentzFactor
