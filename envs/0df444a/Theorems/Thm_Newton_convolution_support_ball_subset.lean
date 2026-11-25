-- Prove2me | Theorems.Thm_Newton_convolution_support_ball_subset
-- name    : Newton.convolution_support_ball_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:48:36.872815+00:00
-- url     : https://prove2.me/theorems/c9ed36d8-b0bd-4fba-bd92-517350afe610
-- title:
--   Newton: convolution support ball subset
-- statement:
--   **Explicit support bound for convolution.**
--
--   If supp(f) ⊆ B_R and supp(g) ⊆ B_δ, then supp(f * g) ⊆ B_{R+δ}.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L692-L732
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L692-L732

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

theorem Newton.convolution_support_ball_subset
    (f g : (Fin n → ℝ) → ℂ)
    (R δ : ℝ)
    (hf_supp : tsupport f ⊆ Metric.closedBall (0 : Fin n → ℝ) R)
    (hg_supp : tsupport g ⊆ Metric.closedBall (0 : Fin n → ℝ) δ) :
    tsupport (fun x => ∫ y, f (x - y) * g y) ⊆
      Metric.closedBall (0 : Fin n → ℝ) (R + δ) := by sorry
