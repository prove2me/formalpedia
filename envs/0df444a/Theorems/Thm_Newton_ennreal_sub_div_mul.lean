-- Prove2me | Theorems.Thm_Newton_ennreal_sub_div_mul
-- name    : Newton.ennreal_sub_div_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:59:59.617835+00:00
-- url     : https://prove2.me/theorems/30ac43cc-99ed-4540-b3b2-77021a5aa17e
-- title:
--   Newton: ennreal sub div mul
-- statement:
--   Auxiliary lemma showing (r - p) / (p * r) = 1/p - 1/r in ENNReal (when p ≤ r)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L194-L204
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L194-L204

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

theorem Newton.ennreal_sub_div_mul {p r : ℝ≥0∞}
    (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ⊤) (hr_pos : r ≠ 0) (hr_ne_top : r ≠ ⊤) :
    (r - p) / (p * r) = 1/p - 1/r := by sorry
