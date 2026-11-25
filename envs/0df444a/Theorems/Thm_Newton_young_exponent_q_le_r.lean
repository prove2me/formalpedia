-- Prove2me | Theorems.Thm_Newton_young_exponent_q_le_r
-- name    : Newton.young_exponent_q_le_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:53.913868+00:00
-- url     : https://prove2.me/theorems/c8b3aa77-766d-46d4-b4ae-5fb82dc656bc
-- title:
--   Newton: young exponent q le r
-- statement:
--   Auxiliary lemma to derive q ≤ r from Young exponent condition
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L154-L158
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L154-L158

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

theorem Newton.young_exponent_q_le_r
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    q ≤ r := by sorry
