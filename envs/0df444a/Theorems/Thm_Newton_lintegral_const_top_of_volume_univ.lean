-- Prove2me | Theorems.Thm_Newton_lintegral_const_top_of_volume_univ
-- name    : Newton.lintegral_const_top_of_volume_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:24:33.556838+00:00
-- url     : https://prove2.me/theorems/4e1d18e5-f839-4217-89d2-6d05981a246a
-- title:
--   Newton: lintegral const top of volume univ
-- statement:
--   For a nonzero constant `c`, the integral of `c` over the whole space is infinite
--   when the dimension `n` is positive.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L293-L299
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L293-L299

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

theorem Newton.lintegral_const_top_of_volume_univ (c : ℝ≥0∞) (hc : c ≠ 0) (hn : 0 < n) :
    ∫⁻ (_ : Fin n → ℝ), c ∂(volume) = ⊤ := by sorry
