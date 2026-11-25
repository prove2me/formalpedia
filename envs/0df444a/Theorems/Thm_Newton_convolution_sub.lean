-- Prove2me | Theorems.Thm_Newton_convolution_sub
-- name    : Newton.convolution_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:51:55.505091+00:00
-- url     : https://prove2.me/theorems/b1e9dda5-63df-4bf3-ac60-28607312a147
-- title:
--   Newton: convolution sub
-- statement:
--   The Newton construction uses the convolution sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L15-L34
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L15-L34

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

theorem Newton.convolution_sub
    (f₁ f₂ g : (Fin n → ℝ) → ℂ)
    (hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * g y) volume)
    (hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * g y) volume) :
    (fun x => ∫ a, (f₁ (x - a) - f₂ (x - a)) * g a) =ᶠ[ae volume]
    (fun x => (∫ a, f₁ (x - a) * g a) - ∫ a, f₂ (x - a) * g a) := by sorry
