-- Prove2me | Theorems.Thm_Newton_tonelli_norm_product_bound
-- name    : Newton.tonelli_norm_product_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:21:16.965232+00:00
-- url     : https://prove2.me/theorems/509cc200-082f-4a1c-8630-947a04cc50c8
-- title:
--   Newton: tonelli norm product bound
-- statement:
--   **Tonelli: Separate Factors**
--
--   For f, g : G → ℂ with appropriate boundedness and a translation-invariant measure μ,
--   ∫⁻ (x,y), ‖f(x-y) * g(y)‖ ∂(μ.prod μ)
--     ≤ (∫⁻ x, ‖f x‖ ∂μ) * (∫⁻ y, ‖g y‖ ∂μ)
--
--   when these integrals are finite.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L170-L288
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L170-L288

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

theorem Newton.tonelli_norm_product_bound
    {f g : G → ℂ}
    [MeasurableAdd₂ G]
    [MeasurableNeg G]
    [μ.IsAddRightInvariant]
    [SFinite μ]
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ)
    (hf_int : ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ < ∞)
    (hg_int : ∫⁻ y, ENNReal.ofReal ‖g y‖ ∂μ < ∞) :
    ∫⁻ p, ENNReal.ofReal ‖f (p.1 - p.2) * g p.2‖ ∂(μ.prod μ) < ∞ := by sorry
