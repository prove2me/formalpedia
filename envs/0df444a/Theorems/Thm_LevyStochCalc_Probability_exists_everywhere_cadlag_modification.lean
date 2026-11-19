-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_exists_everywhere_cadlag_modification
-- name    : LevyStochCalc.Probability.exists_everywhere_cadlag_modification
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T23:36:26.623207+00:00
-- url     : https://prove2.me/theorems/48da7b4a-de16-4571-816f-4437d26284b2
-- title:
--   exists everywhere cadlag modification
-- statement:
--   The source theorem `LevyStochCalc.Probability.exists_everywhere_cadlag_modification` is extracted from `LevyStochCalc.Probability.ProgressiveCadlag`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F001

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

theorem _root_.LevyStochCalc.Probability.exists_everywhere_cadlag_modification
    {P : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {X : ℝ → Ω → ℝ}
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (X t))
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 L)) :
    ∃ Y : ℝ → Ω → ℝ, (∀ t : ℝ, Measurable[ℱ t] (Y t)) ∧ (∀ t : ℝ, Y t =ᵐ[P] X t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))) ∧
      ∀ (ω : Ω) (t : ℝ), ∃ L : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 L) := by sorry
