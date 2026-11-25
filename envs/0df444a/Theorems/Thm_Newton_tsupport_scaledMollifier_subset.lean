-- Prove2me | Theorems.Thm_Newton_tsupport_scaledMollifier_subset
-- name    : Newton.tsupport_scaledMollifier_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:48:30.24747+00:00
-- url     : https://prove2.me/theorems/9b419787-eceb-443f-9781-687f428ad3c1
-- title:
--   Newton: tsupport scaled Mollifier subset
-- statement:
--   T-support inclusion for the scaled mollifier: it is contained in the ball of radius `η`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L119-L172
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L119-L172

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
variable {ψ : (Fin n → ℝ) → ℝ}

theorem Newton.tsupport_scaledMollifier_subset
    (hψ : IsApproximateIdentity ψ) {η : ℝ} (hη_pos : 0 < η) :
    tsupport (scaledMollifier ψ η)
      ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by sorry
