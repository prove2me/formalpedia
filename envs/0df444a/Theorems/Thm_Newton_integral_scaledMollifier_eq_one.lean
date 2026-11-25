-- Prove2me | Theorems.Thm_Newton_integral_scaledMollifier_eq_one
-- name    : Newton.integral_scaledMollifier_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:07:27.112604+00:00
-- url     : https://prove2.me/theorems/7018c49f-fcc6-4ee5-a454-c1cbe8b3e00b
-- title:
--   Newton: integral scaled Mollifier eq one
-- statement:
--   The total mass of the scaled mollifier is 1.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L175-L278
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L175-L278

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

theorem Newton.integral_scaledMollifier_eq_one
    (hψ : IsApproximateIdentity ψ) {η : ℝ} (hη_pos : 0 < η) :
    ∫ x, scaledMollifier ψ η x = (1 : ℝ) := by sorry
