-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_measurable_setIntegral_Icc
-- name    : LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:36:37.68583+00:00
-- url     : https://prove2.me/theorems/e3378254-798e-48ff-a1f7-2eceefd2d6d7
-- title:
--   measurable setIntegral Icc
-- statement:
--   The source theorem `LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc` is extracted from `LevyStochCalc.Probability.ProgressiveCadlag`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Progressive_F002
import Mathlib.MeasureTheory.Function.Floor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right-continuous adapted processes are progressively measurable

An adapted process with right-continuous paths is progressively measurable: on `(-∞, i] × Ω` it
is the pointwise limit of the dyadic right-staircases `t ↦ X_{⌈2ⁿt⌉/2ⁿ ∧ i}`, each of which
takes countably many values, all at times bounded by `i`.

## Main statements

* `Probability.dyadicCeil` — the dyadic right-staircase, capped at a horizon.
* `LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous` — a right-continuous
  adapted process is progressively measurable.
* `LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_uncurry` — a progressively
  measurable process is jointly measurable.
* `LevyStochCalc.Probability.exists_everywhere_cadlag_modification` — under the usual
  conditions, an almost-surely càdlàg adapted process has an everywhere-càdlàg modification.
* `LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc` — the integral
  of a progressively measurable process over `[0, t]` is measurable for `ℱ t`.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {H : Ω → ℝ → ℝ}
    (h : ProgressivelyMeasurable ℱ H) (t : ℝ) :
    Measurable[ℱ t] fun ω => ∫ s in Set.Icc (0 : ℝ) t, H ω s ∂volume := by sorry
