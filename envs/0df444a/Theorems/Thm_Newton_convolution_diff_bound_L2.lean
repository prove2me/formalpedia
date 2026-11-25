-- Prove2me | Theorems.Thm_Newton_convolution_diff_bound_L2
-- name    : Newton.convolution_diff_bound_L2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:40:50.882917+00:00
-- url     : https://prove2.me/theorems/17fb9e6d-9cad-4be9-8b96-7d67c7e4af8c
-- title:
--   Newton: convolution diff bound L2
-- statement:
--   **Bound on difference of convolutions (L² case).**
--
--   ‖(g - f₀) * ψ‖₂ ≤ ‖g - f₀‖₂ · ‖ψ‖₁
--
--   L² version of the above, used for L² error bounds.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L499-L581
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L499-L581

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

theorem Newton.convolution_diff_bound_L2
    (f₁ f₂ ψ : (Fin n → ℝ) → ℂ)
    (hf₁ : MemLp f₁ 2 volume)
    (hf₂ : MemLp f₂ 2 volume)
    (hψ : Integrable ψ volume) :
    eLpNorm (fun x =>
      (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 2 volume ≤
      eLpNorm (fun x => f₁ x - f₂ x) 2 volume * eLpNorm ψ 1 volume := by sorry
