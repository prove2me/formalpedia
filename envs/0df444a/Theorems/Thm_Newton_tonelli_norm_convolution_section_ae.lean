-- Prove2me | Theorems.Thm_Newton_tonelli_norm_convolution_section_ae
-- name    : Newton.tonelli_norm_convolution_section_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:50.883704+00:00
-- url     : https://prove2.me/theorems/9c0934a5-2325-40d8-b717-8ca62720970f
-- title:
--   Newton: tonelli norm convolution section ae
-- statement:
--   **Tonelli for Norm Convolution Kernels (Key Application)**
--
--   For f, g : G → ℂ and measurable norms,
--   if (x,y) ↦ f(x - y) * g(y) is integrable on μ.prod μ,
--   then for a.e. x, y ↦ ‖f(x - y)‖ * ‖g(y)‖ is integrable on μ.
--
--   This theorem bridges from the product-level assumption to the section-level conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L108-L117
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L108-L117

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

theorem Newton.tonelli_norm_convolution_section_ae
    {f g : G → ℂ} [SFinite μ]
    (h_kernel_int : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)) :
    ∀ᵐ x ∂μ, Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ := by sorry
