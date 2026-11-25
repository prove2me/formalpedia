-- Prove2me | Theorems.Thm_Newton_tonelli_nonneg_prod_eq_iterated
-- name    : Newton.tonelli_nonneg_prod_eq_iterated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:56:23.316701+00:00
-- url     : https://prove2.me/theorems/a8e758c2-0a6d-42c2-9dd7-005e48219691
-- title:
--   Newton: tonelli nonneg prod eq iterated
-- statement:
--   **Tonelli's Theorem: Integral Equality on Product Measures**
--
--   For a measurable nonnegative function on a product space,
--   the double integral equals the iterated integral (in any order).
--
--   This is the fundamental statement: If f : G × G → ℝ≥0∞ is measurable and nonnegative,
--   then: ∫⁻ (x,y), f (x,y) ∂(μ.prod μ) = ∫⁻ x, ∫⁻ y, f (x,y) ∂μ ∂μ
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L34-L38
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L34-L38

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

theorem Newton.tonelli_nonneg_prod_eq_iterated
    (f : G × G → ℝ≥0∞)
    (hf_meas : Measurable f) :
    ∫⁻ p, f p ∂(μ.prod μ) = ∫⁻ x, ∫⁻ y, f (x, y) ∂μ ∂μ := by sorry
