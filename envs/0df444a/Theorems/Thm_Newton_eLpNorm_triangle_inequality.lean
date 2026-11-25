-- Prove2me | Theorems.Thm_Newton_eLpNorm_triangle_inequality
-- name    : Newton.eLpNorm_triangle_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:07:15.378804+00:00
-- url     : https://prove2.me/theorems/c470fdaa-262a-46ac-9f5c-06b3f20b4366
-- title:
--   Newton: e Lp Norm triangle inequality
-- statement:
--   **Triangle inequality for Lp norm.**
--
--   ‖f - h‖_p ≤ ‖f - g‖_p + ‖g - h‖_p
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L633-L651
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L633-L651

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

theorem Newton.eLpNorm_triangle_inequality
    (f g h : (Fin n → ℝ) → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hfg : AEStronglyMeasurable (fun x => f x - g x) volume)
    (hgh : AEStronglyMeasurable (fun x => g x - h x) volume) :
    eLpNorm (fun x => f x - h x) p volume ≤
    eLpNorm (fun x => f x - g x) p volume +
    eLpNorm (fun x => g x - h x) p volume := by sorry
