-- Prove2me | Theorems.Thm_Newton_tonelli_ae_section_lt_top
-- name    : Newton.tonelli_ae_section_lt_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:38.940139+00:00
-- url     : https://prove2.me/theorems/8e09fd96-a525-481d-9605-94006a71e769
-- title:
--   Newton: tonelli ae section lt top
-- statement:
--   **Section Finiteness from Product Finiteness (Tonelli Consequence)**
--
--   If ∫⁻ (x,y), f (x,y) ∂(μ.prod μ) < ∞ where f is measurable and nonnegative,
--   then for a.e. x, we have ∫⁻ y, f (x,y) ∂μ < ∞.
--
--   This is the key consequence of Tonelli for our application.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L48-L57
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L48-L57

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

theorem Newton.tonelli_ae_section_lt_top
    {f : G × G → ℝ≥0∞}
    (hf_meas : Measurable f)
    (hf_int : ∫⁻ p, f p ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f (x, y) ∂μ < ∞ := by sorry
