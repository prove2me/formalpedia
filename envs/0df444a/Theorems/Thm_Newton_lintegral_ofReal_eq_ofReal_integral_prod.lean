-- Prove2me | Theorems.Thm_Newton_lintegral_ofReal_eq_ofReal_integral_prod
-- name    : Newton.lintegral_ofReal_eq_ofReal_integral_prod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:56:28.56552+00:00
-- url     : https://prove2.me/theorems/4ff6bd9f-eca8-46a3-b15f-3e6aee053253
-- title:
--   Newton: lintegral of Real eq of Real integral prod
-- statement:
--   Tonelli's theorem for nonnegative real-valued functions on a product space:
--   the lintegral of `ENNReal.ofReal ∘ H` on `μ.prod μ` equals `ENNReal.ofReal` of the
--   iterated Bochner integral when H is nonnegative and AEMeasurable.
--
--   This bridges the gap between ENNReal-valued lintegrals and real-valued iterated integrals.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L887-L909
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L887-L909

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

theorem Newton.lintegral_ofReal_eq_ofReal_integral_prod
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    {H : G × G → ℝ}
    (hH_nonneg : ∀ p, 0 ≤ H p)
    (hH_int : Integrable H (μ.prod μ)) :
    ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) =
      ENNReal.ofReal (∫ x, ∫ y, H (x, y) ∂μ ∂μ) := by sorry
