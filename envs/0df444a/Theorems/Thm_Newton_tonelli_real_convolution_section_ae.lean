-- Prove2me | Theorems.Thm_Newton_tonelli_real_convolution_section_ae
-- name    : Newton.tonelli_real_convolution_section_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:00.792782+00:00
-- url     : https://prove2.me/theorems/cb9618ab-cac4-44ce-a585-39352f066376
-- title:
--   Newton: tonelli real convolution section ae
-- statement:
--   **Tonelli for Real-Valued Convolution Kernels**
--
--   For f, g : G → ℝ and nonnegative values,
--   if (x,y) ↦ f(x - y) * g(y) has finite double integral,
--   then for a.e. x, the section has finite integral.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L126-L148
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L126-L148

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
variable [AddCommGroup G]

theorem Newton.tonelli_real_convolution_section_ae
    {f g : G → ℝ} [MeasurableSub₂ G] [SFinite μ]
    (hf_meas : Measurable f)
    (hg_meas : Measurable g)
    (h_kernel_int : ∫⁻ p, ENNReal.ofReal (|f (p.1 - p.2)| * |g p.2|) ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, ENNReal.ofReal (|f (x - y)| * |g y|) ∂μ < ∞ := by sorry
