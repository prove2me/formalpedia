-- Prove2me | Theorems.Thm_Newton_tonelli_ae_section_lt_top_of_aemeasurable_left
-- name    : Newton.tonelli_ae_section_lt_top_of_aemeasurable_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:34:58.510743+00:00
-- url     : https://prove2.me/theorems/3c299bd7-fbcd-4cf0-b7bf-6686ae59e44b
-- title:
--   Newton: tonelli ae section lt top of aemeasurable left
-- statement:
--   From product finiteness for an `AEMeasurable` nonnegative kernel on `μ.prod μ`,
--   deduce that for a.e. `x`, the section `y ↦ f (x, y)` has finite lintegral.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L303-L333
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L303-L333

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}

theorem Newton.tonelli_ae_section_lt_top_of_aemeasurable_left
    [SFinite μ]
    {f : G × G → ℝ≥0∞}
    (hf_aemeas : AEMeasurable f (μ.prod μ))
    (hf_int : ∫⁻ p, f p ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f (x, y) ∂μ < ∞ := by sorry
