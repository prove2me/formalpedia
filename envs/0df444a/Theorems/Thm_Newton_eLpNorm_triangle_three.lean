-- Prove2me | Theorems.Thm_Newton_eLpNorm_triangle_three
-- name    : Newton.eLpNorm_triangle_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:07:12.784926+00:00
-- url     : https://prove2.me/theorems/0cad3cf9-01f0-4b0d-abaf-59ba74b614d0
-- title:
--   Newton: e Lp Norm triangle three
-- statement:
--   **Three-way triangle inequality (used in proof steps).**
--
--   ‖f - φ‖_p ≤ ‖f - g‖_p + ‖g - ψ‖_p + ‖ψ - φ‖_p
--
--   This is used in the paper's Section 4.2 for the error analysis.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L660-L685
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L660-L685

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

theorem Newton.eLpNorm_triangle_three
    (f g ψ φ : (Fin n → ℝ) → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hfg : AEStronglyMeasurable (fun x => f x - g x) volume)
    (hgψ : AEStronglyMeasurable (fun x => g x - ψ x) volume)
    (hψφ : AEStronglyMeasurable (fun x => ψ x - φ x) volume) :
    eLpNorm (fun x => f x - φ x) p volume ≤
    eLpNorm (fun x => f x - g x) p volume +
    eLpNorm (fun x => g x - ψ x) p volume +
    eLpNorm (fun x => ψ x - φ x) p volume := by sorry
