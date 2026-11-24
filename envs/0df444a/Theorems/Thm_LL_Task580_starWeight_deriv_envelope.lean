-- Prove2me | Theorems.Thm_LL_Task580_starWeight_deriv_envelope
-- name    : LL_Task580.starWeight_deriv_envelope
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T18:13:36.944401+00:00
-- url     : https://prove2.me/theorems/492d0268-efd0-4f88-80ea-088ebce15edd
-- title:
--   Exponential envelope $|\eta_*'(s)|\le 200e^{-46|s|}$
-- statement:
--   For every real $s$, $|\eta_*'(s)|\le 200\,e^{-46|s|}$, where $\eta_*'$ is Mathlib's deriv of $\eta_*$, which is $0$ at any point where $\eta_*$ is not differentiable.
-- source:
--   Helfgott, The ternary Goldbach problem, arXiv 1312.7748v2, page 59 equation 7.16 and page 60 equation 7.20; Lean Lab split of the partial summation numerics.

import Mathlib
import Definitions.Def_LL_Task580_mconv
import Definitions.Def_LL_Task580_eta2
import Definitions.Def_LL_Task580_etaT2
import Definitions.Def_LL_Task580_starWeight

namespace LL_Task580
theorem starWeight_deriv_envelope :
    ∀ s : ℝ, |deriv starWeight s| ≤ 200 * Real.exp (-46 * |s|) := by sorry
end LL_Task580
