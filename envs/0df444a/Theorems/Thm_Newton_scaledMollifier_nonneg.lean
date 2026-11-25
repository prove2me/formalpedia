-- Prove2me | Theorems.Thm_Newton_scaledMollifier_nonneg
-- name    : Newton.scaledMollifier_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:47:28.820255+00:00
-- url     : https://prove2.me/theorems/24a4165a-fce2-44d9-84d3-45a0714ec0ad
-- title:
--   Newton: scaled Mollifier nonneg
-- statement:
--   Nonnegativity of the scaled mollifier when `ψ ≥ 0` and `η ≥ 0`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L42-L49
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L42-L49

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

theorem Newton.scaledMollifier_nonneg
    (hψ_nonneg : ∀ x, 0 ≤ ψ x) {η : ℝ} (hη_nonneg : 0 ≤ η) :
    ∀ x, 0 ≤ scaledMollifier ψ η x := by sorry
