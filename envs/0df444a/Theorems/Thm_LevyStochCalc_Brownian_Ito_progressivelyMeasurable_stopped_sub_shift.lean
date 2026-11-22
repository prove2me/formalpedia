-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_progressivelyMeasurable_stopped_sub_shift
-- name    : LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T09:24:01.9462+00:00
-- url     : https://prove2.me/theorems/67afefc7-1177-4bfc-bea2-5f0ae1422452
-- title:
--   progressivelyMeasurable stopped sub shift
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_shift` is extracted from `LevyStochCalc.Ito.JumpFormulaChainStopped`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CappedJumpSumMeasurable_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Increments read along a random vector known at the earlier stopping time

The increment between two ordered stopping times of an integrand built from a path translated by
a random vector known at the earlier time is supported on the region strictly after that time,
where the translation is already known: there the translated path is the path plus the cut-off
vector, which is measurable for the σ-algebra at the running time because the region is a
countable union of rectangles `{σ ≤ q} × (q, t]`. The increment is therefore progressively
measurable without any restriction on the range of the vector or on that of the stopping times.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_indicator_shiftRegion` — a random vector known at a
  stopping time, cut to the times strictly after it and up to a horizon, is measurable for the
  σ-algebra at that horizon on the product with the time axis.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_shift` — the increment between
  two ordered stopping times of an integrand read along a random vector known at the earlier one
  is progressively measurable.
* `LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub_shift` — that increment has
  measurable uncurrying.
* `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_stopped_sub_cappedJumpSumAt` — the
  increment between consecutive capped arrival times of an integrand read along the capped
  left-limit jump sum is progressively measurable.
* `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_stopped_sub_cappedJumpSumAt` — that
  increment has measurable uncurrying.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory

universe u v

section ShiftRegion

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E] [Zero E]
  {ℱ : Filtration ℝ mΩ} {σ : Ω → WithTop ℝ}

end ShiftRegion

section StoppedShift

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n : ℕ} {ℱ : Filtration ℝ mΩ}
  {σ τ : Ω → WithTop ℝ}

theorem _root_.LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_shift (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {c : Ω → Fin n → ℝ} (hc : Measurable[hσ.measurableSpace] c)
    {V : ℝ → Ω → Fin n → ℝ} (hV : Probability.ProgressivelyMeasurable ℱ fun ω s => V s ω)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) {H : Ω → ℝ → ℝ}
    (hH : Probability.ProgressivelyMeasurable ℱ H) {K : Ω → ℝ → ℝ}
    (hK : ∀ ω s, K ω s = φ (V s ω + c ω) * H ω s) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ K ω s - Probability.stopped σ K ω s := by sorry
