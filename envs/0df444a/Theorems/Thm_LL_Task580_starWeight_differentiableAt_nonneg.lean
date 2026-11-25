-- Prove2me | Theorems.Thm_LL_Task580_starWeight_differentiableAt_nonneg
-- name    : LL_Task580.starWeight_differentiableAt_nonneg
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-25T03:23:20.572442+00:00
-- url     : https://prove2.me/theorems/80285374-988c-43b5-bf02-b3bde462265a
-- title:
--   $\eta_*$ is differentiable on $[0,\infty)$
-- statement:
--   For every real $s\ge0$, $\eta_*$ is differentiable at $s$.
-- source:
--   Helfgott, The ternary Goldbach problem, arXiv 1312.7748v2, page 60 equation 7.20; Lean Lab split.

import Mathlib
import Definitions.Def_LL_Task580_mconv
import Definitions.Def_LL_Task580_eta2
import Definitions.Def_LL_Task580_etaT2
import Definitions.Def_LL_Task580_starWeight

namespace LL_Task580
theorem starWeight_differentiableAt_nonneg :
    ∀ s : ℝ, 0 ≤ s → DifferentiableAt ℝ starWeight s := by sorry
end LL_Task580
