-- Prove2me | Theorems.Thm_MeasureTheory_setLIntegral_le_rpow_lintegral_sq_mul_rpow
-- name    : MeasureTheory.setLIntegral_le_rpow_lintegral_sq_mul_rpow
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:52:43.957494+00:00
-- url     : https://prove2.me/theorems/884297a4-651f-4364-8dea-502c17975af4
-- title:
--   Set-restricted Cauchy-Schwarz bound for nonnegative extended-real integrals
-- statement:
--   Let μ be a measure on a measurable space Ω, Z : Ω → [0, ∞] be μ-almost everywhere measurable, and A ⊆ Ω be measurable. The integral of Z over A is at most the square root of the second moment of Z times the square root of μ(A). This is the measurable-set Cauchy–Schwarz estimate, including infinite-valued integrals. Ported verbatim in substance from Scott Armstrong's MarkovProcess project (Apache-2.0); source and commit are recorded.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Analysis/PaleyZygmund.lean#L39-L68

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open scoped ENNReal NNReal
open MeasureTheory
variable {Omega : Type*} [MeasurableSpace Omega]

theorem MeasureTheory.setLIntegral_le_rpow_lintegral_sq_mul_rpow (mu : Measure Omega) {Z : Omega → ℝ≥0∞}
    (hZ : AEMeasurable Z mu) {A : Set Omega} (hA : MeasurableSet A) :
    ∫⁻ omega in A, Z omega ∂mu ≤
      (∫⁻ omega, Z omega ^ 2 ∂mu) ^ (1 / 2 : ℝ) * (mu A) ^ (1 / 2 : ℝ) := by sorry
