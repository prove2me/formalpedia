-- Prove2me | Theorems.Thm_Newton_tonelli_product_ae_section_lt_top
-- name    : Newton.tonelli_product_ae_section_lt_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:19:33.86871+00:00
-- url     : https://prove2.me/theorems/d3398616-e016-4c77-96e1-6a1942691c50
-- title:
--   Newton: tonelli product ae section lt top
-- statement:
--   **Tonelli for Norm Products (Nonnegative)**
--
--   For measurable nonnegative functions `f, g : G → ℝ≥0∞`,
--   if `∫⁻ (x, y), f x * g y ∂(μ.prod μ) < ∞`,
--   then for a.e. `x`, `∫⁻ y, f x * g y ∂μ < ∞`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L66-L86
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L66-L86

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
variable [SFinite μ]

theorem Newton.tonelli_product_ae_section_lt_top
    {f g : G → ℝ≥0∞}
    (hf_meas : Measurable f)
    (hg_meas : Measurable g)
    (hf_int : ∫⁻ x, f x ∂μ < ∞)
    (hg_int : ∫⁻ y, g y ∂μ < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f x * g y ∂μ < ∞ := by sorry
