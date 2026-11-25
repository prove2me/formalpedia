-- Prove2me | Theorems.Thm_Newton_tonelli_ae_section_lt_top_of_aemeasurable_right
-- name    : Newton.tonelli_ae_section_lt_top_of_aemeasurable_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:20.235821+00:00
-- url     : https://prove2.me/theorems/0de63f11-9e79-42e0-8738-91d3c93aefd5
-- title:
--   Newton: tonelli ae section lt top of aemeasurable right
-- statement:
--   Symmetric version: from product finiteness for an `AEMeasurable` nonnegative kernel,
--   deduce that for a.e. `y`, the section `x ↦ f (x, y)` has finite lintegral.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L339-L409
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L339-L409

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

theorem Newton.tonelli_ae_section_lt_top_of_aemeasurable_right
    [SFinite μ]
    {f : G × G → ℝ≥0∞}
    (hf_aemeas : AEMeasurable f (μ.prod μ))
    (hf_int : ∫⁻ p, f p ∂(μ.prod μ) < ∞) :
    ∀ᵐ y ∂μ, ∫⁻ x, f (x, y) ∂μ < ∞ := by sorry
