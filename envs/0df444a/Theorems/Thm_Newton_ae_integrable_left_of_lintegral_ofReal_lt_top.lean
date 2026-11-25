-- Prove2me | Theorems.Thm_Newton_ae_integrable_left_of_lintegral_ofReal_lt_top
-- name    : Newton.ae_integrable_left_of_lintegral_ofReal_lt_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:24.670807+00:00
-- url     : https://prove2.me/theorems/41004d93-cbb9-43b7-bfdb-03807622b5e6
-- title:
--   Newton: ae integrable left of lintegral of Real lt top
-- statement:
--   From product finiteness for an `AEMeasurable` nonnegative real-valued kernel on `μ.prod μ`,
--   deduce that for a.e. `x`, the section `y ↦ H (x, y)` is Bochner integrable (as an ℝ-valued
--   function).
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L418-L481
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L418-L481

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

theorem Newton.ae_integrable_left_of_lintegral_ofReal_lt_top
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    {H : G × G → ℝ}
    (hH_nonneg : ∀ p, 0 ≤ H p)
    (hH_aemeas : AEMeasurable H (μ.prod μ))
    (hH_int :
      ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, Integrable (fun y => H (x, y)) μ := by sorry
