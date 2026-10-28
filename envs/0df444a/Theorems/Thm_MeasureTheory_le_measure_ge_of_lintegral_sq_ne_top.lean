-- Prove2me | Theorems.Thm_MeasureTheory_le_measure_ge_of_lintegral_sq_ne_top
-- name    : MeasureTheory.le_measure_ge_of_lintegral_sq_ne_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:07:57.743993+00:00
-- url     : https://prove2.me/theorems/8b782202-db3d-4cd3-a4bf-f6f22d3b9d1f
-- title:
--   Paley-Zygmund inequality with a finite second moment
-- statement:
--   For a measurable nonnegative extended-real random variable on a probability space with finite second moment, the mass exceeding rho times the mean is at least the Paley-Zygmund ratio of the truncated first-moment square to the second moment. The zero second-moment case is handled by the division convention for extended nonnegative reals. Source: Scott Armstrong's Apache-2.0 MarkovProcess library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Analysis/PaleyZygmund.lean#L123-L133

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_MeasureTheory_lintegral_le_rpow_lintegral_sq
import Theorems.Thm_MeasureTheory_lintegral_sq_mul_measure_ge_le

open scoped ENNReal NNReal
open MeasureTheory
variable {Omega : Type*} [MeasurableSpace Omega]

theorem MeasureTheory.le_measure_ge_of_lintegral_sq_ne_top (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) (hsq : ∫⁻ omega, Z omega ^ 2 ∂mu ≠ ⊤)
    (rho : ℝ≥0) :
    ((1 : ℝ≥0∞) - rho) ^ 2 * (∫⁻ omega, Z omega ∂mu) ^ 2 / (∫⁻ omega, Z omega ^ 2 ∂mu) ≤
      mu {omega | (rho : ℝ≥0∞) * ∫⁻ omega, Z omega ∂mu ≤ Z omega} := by sorry
