-- Prove2me | Theorems.Thm_Newton_convolution_diff_bound_L1
-- name    : Newton.convolution_diff_bound_L1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:15:11.059682+00:00
-- url     : https://prove2.me/theorems/39df0fc7-0e5e-45c9-8492-1625c47c94fb
-- title:
--   Newton: convolution diff bound L1
-- statement:
--   **Bound on difference of convolutions (L¹ case).**
--
--   ‖(g - f₀) * ψ‖₁ ≤ ‖g - f₀‖₁ · ‖ψ‖₁
--
--   Corresponds to h_conv_diff_bound in the code.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L308-L358
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L308-L358

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Definitions.Def_Newton_Analysis_Convolution_Bounds
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise
open Newton
variable {n : ℕ}

theorem Newton.convolution_diff_bound_L1
    (f₁ f₂ ψ : (Fin n → ℝ) → ℂ)
    (hf₁ : Integrable f₁ volume)
    (hf₂ : Integrable f₂ volume)
    (hψ : Integrable ψ volume) :
    eLpNorm (fun x =>
      (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 1 volume ≤
      eLpNorm (fun x => f₁ x - f₂ x) 1 volume * eLpNorm ψ 1 volume := by sorry
