-- Prove2me | Theorems.Thm_Newton_lintegral_ofReal_le_ofReal_integral_prod
-- name    : Newton.lintegral_ofReal_le_ofReal_integral_prod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:21:54.456328+00:00
-- url     : https://prove2.me/theorems/a5329bdd-5290-494f-af0f-1a31f89ecdbf
-- title:
--   Newton: lintegral of Real le of Real integral prod
-- statement:
--   Upper bound version of Tonelli for nonnegative functions:
--   the lintegral of `ENNReal.ofReal ∘ H` equals `ENNReal.ofReal` of the iterated integral
--   when H is nonnegative, AEMeasurable, and has finite lintegral.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L916-L943
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L916-L943

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

theorem Newton.lintegral_ofReal_le_ofReal_integral_prod
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    {H : G × G → ℝ}
    (hH_nonneg : ∀ p, 0 ≤ H p)
    (hH_aemeas : AEMeasurable H (μ.prod μ))
    (hH_lt_top : ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) < ⊤) :
    ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) ≤
      ENNReal.ofReal (∫ x, ∫ y, H (x, y) ∂μ ∂μ) := by sorry
