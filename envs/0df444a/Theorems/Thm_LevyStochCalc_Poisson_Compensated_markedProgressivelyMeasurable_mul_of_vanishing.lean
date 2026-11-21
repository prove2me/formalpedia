-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_markedProgressivelyMeasurable_mul_of_vanishing
-- name    : LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_mul_of_vanishing
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:41:37.795546+00:00
-- url     : https://prove2.me/theorems/05fd4dfa-0ae2-4908-ae26-6cd3d2e6547f
-- title:
--   markedProgressivelyMeasurable mul of vanishing
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_mul_of_vanishing` is extracted from `LevyStochCalc.Poisson.CompensatedPullOut`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside a compensated integral

A bounded weight measurable at time `a` times the compensated integral of a marked integrand
vanishing up to `a` is the compensated integral of the weighted integrand. The identity is proved
in `L²`: the squared distance between the two sides expands, through the Itô–Lévy isometry and
the quadratic-variation martingale started at `a`, into a combination of weighted compensators
that cancels.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Vanishing

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤)

end Vanishing

section Weighted

theorem _root_.LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_mul_of_vanishing {φ : Ω → ℝ → E → ℝ}
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ) {a : ℝ}
    (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) {V : Ω → ℝ} (hVm : StronglyMeasurable[ℱ a] V) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => V ω * φ ω s e := by sorry
