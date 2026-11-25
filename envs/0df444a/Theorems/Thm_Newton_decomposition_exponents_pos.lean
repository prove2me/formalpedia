-- Prove2me | Theorems.Thm_Newton_decomposition_exponents_pos
-- name    : Newton.decomposition_exponents_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:00:05.782293+00:00
-- url     : https://prove2.me/theorems/3354b33d-551c-451a-9f3c-287bf3857d28
-- title:
--   Newton: decomposition exponents pos
-- statement:
--   Verify that exponents used in decomposition are non-negative (can be 0 at boundary)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L276-L289
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L276-L289

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

theorem Newton.decomposition_exponents_pos
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr_ne_top : r ≠ ⊤) :
    0 < p/r ∧ 0 < q/r ∧ 0 ≤ 1 - p/r ∧ 0 ≤ 1 - q/r := by sorry
