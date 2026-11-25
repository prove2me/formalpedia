-- Prove2me | Theorems.Thm_Newton_integral_norm_eq_toReal_lintegral
-- name    : Newton.integral_norm_eq_toReal_lintegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:25.890822+00:00
-- url     : https://prove2.me/theorems/6da160c0-6414-4a72-b326-cd34709f3e8a
-- title:
--   Newton: integral norm eq to Real lintegral
-- statement:
--   Relate the integral of the norm of an integrable function with the corresponding lintegral.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Minkowski.lean#L21-L32
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Minkowski.lean#L21-L32

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal
open Newton
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E]

theorem Newton.integral_norm_eq_toReal_lintegral
    [NormedSpace ℝ E] {f : α → E} (hf : Integrable f μ) :
    ∫ x, ‖f x‖ ∂μ = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal := by sorry
