-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_mul_setIntegral_Ioc
-- name    : LevyStochCalc.Probability.integral_mul_setIntegral_Ioc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:26:49.425712+00:00
-- url     : https://prove2.me/theorems/9dcee118-4966-4a73-b8f5-3e4189c54066
-- title:
--   integral mul setIntegral Ioc
-- statement:
--   The source theorem `LevyStochCalc.Probability.integral_mul_setIntegral_Ioc` is extracted from `LevyStochCalc.Probability.PairingFubini`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing an integrable weight against a time integral

For an integrable weight and a bounded jointly measurable process on a bounded time interval, the
expectation of the weight against the time integral of the process is the time integral of the
expectations.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

theorem _root_.LevyStochCalc.Probability.integral_mul_setIntegral_Ioc {a t : ℝ} {Z : Ω → ℂ} (hZm : Measurable Z)
    (hZ : Integrable Z P) {Φ : Ω → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ))
    {C : ℝ} (hC : ∀ ω u, ‖Φ ω u‖ ≤ C) :
    ∫ ω, Z ω * (∫ u in Set.Ioc a t, Φ ω u) ∂P
      = ∫ u in Set.Ioc a t, (∫ ω, Z ω * Φ ω u ∂P) := by sorry
