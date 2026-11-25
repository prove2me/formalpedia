-- Prove2me | Theorems.Thm_Newton_young_exponent_p_le_r
-- name    : Newton.young_exponent_p_le_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:55.584374+00:00
-- url     : https://prove2.me/theorems/de5df998-2126-4cd6-a575-57c9c24a1db4
-- title:
--   Newton: young exponent p le r
-- statement:
--   The Newton construction uses the young exponent p le r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L129-L151
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L129-L151

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

theorem Newton.young_exponent_p_le_r
    {p q r : ℝ≥0∞} (hq : 1 ≤ q) (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    p ≤ r := by sorry
