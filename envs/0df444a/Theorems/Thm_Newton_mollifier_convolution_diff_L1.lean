-- Prove2me | Theorems.Thm_Newton_mollifier_convolution_diff_L1
-- name    : Newton.mollifier_convolution_diff_L1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:15:06.506893+00:00
-- url     : https://prove2.me/theorems/d10bdb45-b700-4d76-978e-38c686f01c42
-- title:
--   Newton: mollifier convolution diff L1
-- statement:
--   **Bound on difference of convolutions with a normalized mollifier (L¹ case).**
--
--   If ψ is a non-negative mollifier with unit mass, convolution with the scaled
--   ψ does not increase the L¹ distance between two functions.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L366-L490
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L366-L490

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

theorem Newton.mollifier_convolution_diff_L1
    (g f₀ : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hg : Integrable g volume)
    (hf₀ : Integrable f₀ volume)
    (hψ_nonneg : ∀ x, 0 ≤ ψ x)
    (hψ_int : ∫ x, ψ x = 1) :
    ∀ η : ℝ, 0 < η → η < 1 →
      eLpNorm (fun x =>
        (∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) -
        (∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)))
        1 volume ≤
      eLpNorm (fun x => g x - f₀ x) 1 volume := by sorry
