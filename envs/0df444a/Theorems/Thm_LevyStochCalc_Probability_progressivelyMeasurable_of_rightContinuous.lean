-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_progressivelyMeasurable_of_rightContinuous
-- name    : LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:35:38.832714+00:00
-- url     : https://prove2.me/theorems/b86fe40e-f205-414c-b4e5-3a5fd3cede70
-- title:
--   progressivelyMeasurable of rightContinuous
-- statement:
--   The source theorem `LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous` is extracted from `LevyStochCalc.Probability.ProgressiveCadlag`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000

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

theorem _root_.LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → ℝ}
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (X t))
    (hright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))) :
    ProgressivelyMeasurable ℱ (fun ω s => X s ω) := by sorry
