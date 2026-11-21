-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_MarkedPredictable_comp_measurable
-- name    : LevyStochCalc.Probability.MarkedPredictable.comp_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:15:35.914041+00:00
-- url     : https://prove2.me/theorems/70d9098d-22dd-46c6-8b7a-fbbd0a4eedf0
-- title:
--   comp measurable
-- statement:
--   The source theorem `LevyStochCalc.Probability.MarkedPredictable.comp_measurable` is extracted from `LevyStochCalc.Probability.MarkedPredictableComp`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Marked predictability under measurable post-composition

On the positive times the time coordinate of the time–mark space is measurable for the marked
predictable σ-algebra, a predictable process of the time and the sample point lifts to a marked
predictable one, and a marked predictable process keeps its measurability. A measurable function
of the time, a predictable process and a marked predictable process is therefore marked
predictable once it is cut to the positive times.

## Main statements

* `LevyStochCalc.Probability.measurableSet_markedPredictableSigma_time_pos` — a measurable set
  of positive times, carrying all sample points and marks, is marked predictable.
* `LevyStochCalc.Probability.measurable_markedPredictableSigma_time_pos` — the time coordinate,
  cut to the positive times, is marked predictable.
* `LevyStochCalc.Probability.MarkedPredictable.comp_measurable` — a measurable function of the
  time, a predictable process and a marked predictable process, cut to the positive times, is
  marked predictable.
* `LevyStochCalc.Probability.MarkedPredictable.comp_continuous` — the same for a continuous
  function.

## References

* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
  {E : Type v} [MeasurableSpace E] {ν : Measure E}

section Time

end Time

section Comp

theorem _root_.LevyStochCalc.Probability.MarkedPredictable.comp_measurable [SigmaFinite ν] {F₁ : Type*} {F₂ : Type*}
    {F₃ : Type*} [MeasurableSpace F₁] [MeasurableSpace F₂] [MeasurableSpace F₃] [Zero F₃]
    {F : ℝ × F₁ × F₂ → F₃} (hF : Measurable F) {Y : Ω → ℝ → F₁}
    (hY : Measurable[predictableSigma ℱ] fun q : ℝ × Ω => Y q.2 q.1)
    {Γ : Ω → ℝ → E → F₂} (hΓ : MarkedPredictable ℱ ν Γ) :
    MarkedPredictable ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      if 0 < s then F (s, Y ω s, Γ ω s e) else 0 := by sorry
