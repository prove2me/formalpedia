-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_wPlus_at_cddp
-- name    : FriedCrossing.TwinRate.wPlus_at_cddp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:56.073639+00:00
-- url     : https://prove2.me/theorems/23cfd2a6-25c2-5a67-a0b6-63e338fdf350
-- title:
--   Twin Rate: w Plus at cddp
-- statement:
--   At the CDDP point (a, b) = (r₀, 0) with r₀ > 0 the two first-order rates are r₀ and 0.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L91-L93
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L91-L93

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.wPlus_at_cddp {r₀ : ℝ} (hr₀ : 0 < r₀) : wPlus r₀ 0 = r₀ := by sorry
