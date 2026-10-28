-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_le_rpow_lintegral_sq
-- name    : MeasureTheory.lintegral_le_rpow_lintegral_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:02:29.979377+00:00
-- url     : https://prove2.me/theorems/bdccd5fe-798a-4ef3-ab46-f61113c95644
-- title:
--   Finite first moment bounded by the square root of the second moment
-- statement:
--   Let Z be an almost everywhere measurable nonnegative extended-real random variable on a probability space. Its expected value is bounded above by the square root of its second moment. The proof specializes the source project's set-restricted Cauchy-Schwarz inequality to the universal measurable set. Ported from Scott Armstrong's Apache-2.0 MarkovProcess library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Analysis/PaleyZygmund.lean#L71-L76

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

theorem MeasureTheory.lintegral_le_rpow_lintegral_sq (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ≥0∞} (hZ : AEMeasurable Z mu) :
    ∫⁻ omega, Z omega ∂mu ≤ (∫⁻ omega, Z omega ^ 2 ∂mu) ^ (1 / 2 : ℝ) := by sorry
