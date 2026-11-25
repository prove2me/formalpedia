-- Prove2me | Theorems.Thm_Newton_ennreal_div_mul_right
-- name    : Newton.ennreal_div_mul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:10.163852+00:00
-- url     : https://prove2.me/theorems/94894cd0-df8d-498c-8ac2-20fa9dcf14e3
-- title:
--   Newton: ennreal div mul right
-- statement:
--   Auxiliary lemma showing r / (p * r) = 1/p in ENNReal
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L179-L184
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L179-L184

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}

theorem Newton.ennreal_div_mul_right {p r : ℝ≥0∞}
    (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ⊤) (hr_pos : r ≠ 0) (hr_ne_top : r ≠ ⊤) :
    r / (p * r) = 1 / p := by sorry
