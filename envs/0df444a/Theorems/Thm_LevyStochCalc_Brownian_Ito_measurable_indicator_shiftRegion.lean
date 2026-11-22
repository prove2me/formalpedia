-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_measurable_indicator_shiftRegion
-- name    : LevyStochCalc.Brownian.Ito.measurable_indicator_shiftRegion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T09:23:36.17449+00:00
-- url     : https://prove2.me/theorems/505d159e-1f23-4877-9152-72edcccb6e69
-- title:
--   measurable indicator shiftRegion
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.measurable_indicator_shiftRegion` is extracted from `LevyStochCalc.Ito.JumpFormulaChainStopped`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.Brownian.Ito.measurable_indicator_shiftRegion (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    {c : Ω → E} (hc : Measurable[hσ.measurableSpace] c) (t : ℝ) :
    Measurable[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance]
      (Set.indicator {p : Ω × ℝ | σ p.1 < ((p.2 : ℝ) : WithTop ℝ) ∧ p.2 ≤ t}
        fun p => c p.1) := by sorry
