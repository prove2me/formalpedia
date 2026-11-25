-- Prove2me | Theorems.Thm_Newton_scaled_mollifier_L1_norm_one
-- name    : Newton.scaled_mollifier_L1_norm_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:14:57.01912+00:00
-- url     : https://prove2.me/theorems/1289a436-59ea-480d-b033-db62ff56da92
-- title:
--   Newton: scaled mollifier L1 norm one
-- statement:
--   For the scaled mollifier ψ_η with ∫ ψ = 1, we have ‖ψ_η‖₁ = 1.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L59-L299
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L59-L299

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

theorem Newton.scaled_mollifier_L1_norm_one
    (ψ : (Fin n → ℝ) → ℝ)
    (η : ℝ)
    (hη : 0 < η)
    (hψ_int : Integrable ψ volume)
    (hψ_norm : ∫ x, ψ x = 1)
    (hψ_nonneg : ∀ x, 0 ≤ ψ x) :
    eLpNorm (fun (x : Fin n → ℝ) => η^(-(n : ℝ)) * ψ (fun i => x i / η)) 1 volume =
      ENNReal.ofReal 1 := by sorry
