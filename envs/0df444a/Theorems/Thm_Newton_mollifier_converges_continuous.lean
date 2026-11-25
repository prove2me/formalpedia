-- Prove2me | Theorems.Thm_Newton_mollifier_converges_continuous
-- name    : Newton.mollifier_converges_continuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:07:14.224552+00:00
-- url     : https://prove2.me/theorems/132f4420-ca17-41d0-a562-74ba88448ac1
-- title:
--   Newton: mollifier converges continuous
-- statement:
--   **Mollifier convergence for continuous functions.**
--
--   For f continuous with compact support and ψ an approximate identity:
--     ‖f - f * ψ_η‖_∞ → 0 as η → 0
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L314-L626
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L314-L626

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

theorem Newton.mollifier_converges_continuous
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hf_cont : Continuous f)
    (hf_compact : HasCompactSupport f)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      ∀ x, ‖f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)‖ < ε := by sorry
