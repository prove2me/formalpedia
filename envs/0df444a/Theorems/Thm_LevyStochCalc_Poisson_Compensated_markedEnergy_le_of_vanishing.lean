-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_markedEnergy_le_of_vanishing
-- name    : LevyStochCalc.Poisson.Compensated.markedEnergy_le_of_vanishing
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:32:13.716086+00:00
-- url     : https://prove2.me/theorems/5db04da5-8022-4715-884a-363189f74b45
-- title:
--   markedEnergy le of vanishing
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.markedEnergy_le_of_vanishing` is extracted from `LevyStochCalc.Poisson.CompensatedIntegrandComplete`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the marked integrands

The marked energy of an integrand over a horizon is the square of its `L²`-seminorm for the
product of the sample measure, Lebesgue measure on the horizon and the mark measure. That space is
complete, so an energy-Cauchy sequence of admissible marked integrands has a limit; a pointwise
`limsup` along an almost-everywhere convergent subsequence provides a genuinely progressively
measurable representative of it.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [IsProbabilityMeasure P] [SigmaFinite ν] in

theorem _root_.LevyStochCalc.Poisson.Compensated.markedEnergy_le_of_vanishing {φ : Ω → ℝ → E → ℝ} {T : ℝ}
    (hz : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → φ ω s e = 0) (T' : ℝ) :
    markedEnergy P ν T' φ ≤ markedEnergy P ν T φ := by sorry
