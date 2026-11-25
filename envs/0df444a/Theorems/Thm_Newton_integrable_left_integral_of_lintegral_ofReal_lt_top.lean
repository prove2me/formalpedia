-- Prove2me | Theorems.Thm_Newton_integrable_left_integral_of_lintegral_ofReal_lt_top
-- name    : Newton.integrable_left_integral_of_lintegral_ofReal_lt_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:21:32.621801+00:00
-- url     : https://prove2.me/theorems/e3d22195-5cc2-483e-8ca5-35beb2c13522
-- title:
--   Newton: integrable left integral of lintegral of Real lt top
-- statement:
--   From product finiteness for an `AEMeasurable` nonnegative real-valued kernel on `μ.prod μ`,
--   deduce that the outer integral `x ↦ ∫ y, H (x, y) dμ` is Bochner integrable on `μ`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L487-L559
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L487-L559

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

theorem Newton.integrable_left_integral_of_lintegral_ofReal_lt_top
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    {H : G × G → ℝ}
    (hH_nonneg : ∀ p, 0 ≤ H p)
    (hH_aemeas : AEMeasurable H (μ.prod μ))
    (hH_int :
      ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) < ∞) :
    Integrable (fun x => ∫ y, H (x, y) ∂μ) μ := by sorry
