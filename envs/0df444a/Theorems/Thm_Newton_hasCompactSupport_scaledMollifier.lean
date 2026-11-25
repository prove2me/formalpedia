-- Prove2me | Theorems.Thm_Newton_hasCompactSupport_scaledMollifier
-- name    : Newton.hasCompactSupport_scaledMollifier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:47:40.8178+00:00
-- url     : https://prove2.me/theorems/3c3ad171-3706-48c8-baa5-90c21630f7c9
-- title:
--   Newton: has Compact Support scaled Mollifier
-- statement:
--   Compact support of the scaled mollifier under `η > 0`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L52-L116
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L52-L116

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

theorem Newton.hasCompactSupport_scaledMollifier
    (hψ : HasCompactSupport ψ) {η : ℝ} (hη_pos : 0 < η) :
    HasCompactSupport (scaledMollifier ψ η) := by sorry
