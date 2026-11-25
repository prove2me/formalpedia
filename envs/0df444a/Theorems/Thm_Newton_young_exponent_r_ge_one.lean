-- Prove2me | Theorems.Thm_Newton_young_exponent_r_ge_one
-- name    : Newton.young_exponent_r_ge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:33.86882+00:00
-- url     : https://prove2.me/theorems/7018e150-0ced-4e02-b881-d106587e8208
-- title:
--   Newton: young exponent r ge one
-- statement:
--   Auxiliary lemma to derive r ≥ 1 from Young exponent condition
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L161-L176
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L161-L176

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

theorem Newton.young_exponent_r_ge_one
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    1 ≤ r := by sorry
