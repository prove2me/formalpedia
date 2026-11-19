-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_mul_setIntegral_swap
-- name    : LevyStochCalc.Probability.integral_mul_setIntegral_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:26:57.367568+00:00
-- url     : https://prove2.me/theorems/672737f7-d9fa-4845-9364-df27cb967ee0
-- title:
--   integral mul setIntegral swap
-- statement:
--   The source theorem `LevyStochCalc.Probability.integral_mul_setIntegral_swap` is extracted from `LevyStochCalc.Probability.PairingFubini`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

section Swap

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]

theorem _root_.LevyStochCalc.Probability.integral_mul_setIntegral_swap {S : Set Y} (hSfin : μ S ≠ ⊤)
    {Z : Ω → ℝ} (hZ1 : Integrable Z P) {V : Ω → ℝ} (hVm : AEStronglyMeasurable V P)
    {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv)
    {F : Ω → Y → ℝ} (hFm : Measurable (Function.uncurry F))
    {MF : ℝ} (hFb : ∀ ω y, |F ω y| ≤ MF) :
    ∫ ω, Z ω * V ω * (∫ y in S, F ω y ∂μ) ∂P
      = ∫ y in S, ∫ ω, Z ω * V ω * F ω y ∂P ∂μ := by sorry
