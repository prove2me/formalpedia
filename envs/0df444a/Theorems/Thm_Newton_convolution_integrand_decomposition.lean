-- Prove2me | Theorems.Thm_Newton_convolution_integrand_decomposition
-- name    : Newton.convolution_integrand_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:00:08.350429+00:00
-- url     : https://prove2.me/theorems/1ac9dd8a-c477-42f7-99d3-1f8250483790
-- title:
--   Newton: convolution integrand decomposition
-- statement:
--   The Newton construction uses the convolution integrand decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L381-L512
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L381-L512

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

theorem Newton.convolution_integrand_decomposition
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hp_ne_top : p ≠ ⊤) (hq_ne_top : q ≠ ⊤) (hr_ne_top : r ≠ ⊤)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (x y : Fin n → ℝ) :
    ‖f y‖ * ‖g (x - y)‖ =
      (‖f y‖^(p/r).toReal * ‖g (x - y)‖^(q/r).toReal) *
      ‖f y‖^(1 - p/r).toReal *
      ‖g (x - y)‖^(1 - q/r).toReal := by sorry
