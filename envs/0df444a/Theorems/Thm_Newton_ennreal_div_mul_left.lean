-- Prove2me | Theorems.Thm_Newton_ennreal_div_mul_left
-- name    : Newton.ennreal_div_mul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:00:05.02008+00:00
-- url     : https://prove2.me/theorems/4fd6cb01-c754-413f-96c3-c84eb766a14a
-- title:
--   Newton: ennreal div mul left
-- statement:
--   Auxiliary lemma showing p / (p * r) = 1/r in ENNReal
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L187-L191
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L187-L191

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

theorem Newton.ennreal_div_mul_left {p r : ℝ≥0∞}
    (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ⊤) (hr_pos : r ≠ 0) (hr_ne_top : r ≠ ⊤) :
    p / (p * r) = 1 / r := by sorry
