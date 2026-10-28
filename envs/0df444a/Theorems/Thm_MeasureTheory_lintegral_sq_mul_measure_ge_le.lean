-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_sq_mul_measure_ge_le
-- name    : MeasureTheory.lintegral_sq_mul_measure_ge_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:03:36.260562+00:00
-- url     : https://prove2.me/theorems/5a76541e-dac4-439e-8f7a-c393f64ec78a
-- title:
--   Paley-Zygmund inequality in division-free form
-- statement:
--   For a measurable nonnegative extended-real random variable Z on a probability space with finite first moment and threshold rho, the squared truncated factor (1-rho) times the squared expectation is at most the second moment times the probability that Z exceeds rho times its expectation. This is the division-free Paley-Zygmund inequality, with extended-real arithmetic. Ported with attribution from Scott Armstrong's MarkovProcess project (Apache-2.0).
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Analysis/PaleyZygmund.lean#L81-L120

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_MeasureTheory_setLIntegral_le_rpow_lintegral_sq_mul_rpow

open scoped ENNReal NNReal
open MeasureTheory
variable {Omega : Type*} [MeasurableSpace Omega]

theorem MeasureTheory.lintegral_sq_mul_measure_ge_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) (hfin : ∫⁻ omega, Z omega ∂mu ≠ ⊤) (rho : ℝ≥0) :
    ((1 : ℝ≥0∞) - rho) ^ 2 * (∫⁻ omega, Z omega ∂mu) ^ 2 ≤
      (∫⁻ omega, Z omega ^ 2 ∂mu) *
        mu {omega | (rho : ℝ≥0∞) * ∫⁻ omega, Z omega ∂mu ≤ Z omega} := by sorry
