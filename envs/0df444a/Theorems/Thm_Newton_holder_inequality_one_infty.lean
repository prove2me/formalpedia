-- Prove2me | Theorems.Thm_Newton_holder_inequality_one_infty
-- name    : Newton.holder_inequality_one_infty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:01:15.669258+00:00
-- url     : https://prove2.me/theorems/6b82d082-9412-47a7-88b5-456594c343e8
-- title:
--   Newton: holder inequality one infty
-- statement:
--   **Hölder's inequality (basic form for p = 1, q = ∞).**
--
--   For any measurable functions f and g:
--     ∫ |f · g| dμ ≤ ‖f‖_{L^1} · ‖g‖_{L^∞}
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Holder.lean#L36-L139
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Holder.lean#L36-L139

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
open Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Newton.holder_inequality_one_infty
    (f : α → E) (g : α → F)
    (hf : Integrable f μ)
    (hg_ae : AEStronglyMeasurable g μ)
    (hg_bound : ∃ C, ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (∫ x, ‖f x‖ ∂μ) * (sInf {C | ∀ᵐ x ∂μ, ‖g x‖ ≤ C}) := by sorry
