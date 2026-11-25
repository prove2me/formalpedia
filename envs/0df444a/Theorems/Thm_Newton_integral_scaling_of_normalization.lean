-- Prove2me | Theorems.Thm_Newton_integral_scaling_of_normalization
-- name    : Newton.integral_scaling_of_normalization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:11:55.229784+00:00
-- url     : https://prove2.me/theorems/0f26e749-03a1-4f1d-a13b-5deaf9b500d6
-- title:
--   Newton: integral scaling of normalization
-- statement:
--   Pulling out a scalar when comparing `f` and its normalisation.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L542-L567
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L542-L567

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Newton.integral_scaling_of_normalization
    {f g : α → ℝ} {c : ℝ} (hc_ne_zero : c ≠ 0)
    (h_int : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) =
      c * (∫ x, ((1 / c) * f x) * g x ∂μ) := by sorry
