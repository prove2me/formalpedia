-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_progressivelyMeasurable_indicator_Icc
-- name    : LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indicator_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:13:37.202794+00:00
-- url     : https://prove2.me/theorems/0a89a669-a072-4474-8a42-c2e1cf3bca11
-- title:
--   progressivelyMeasurable indicator Icc
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indicator_Icc` is extracted from `LevyStochCalc.Brownian.ItoIntegrandComplete`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F000
import Definitions.Def_LevyStochCalc_Probability_Progressive_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the admissible integrands on a horizon

The energy of an integrand over `[0, T]` is the square of its `L²`-seminorm for the product of
the sample measure with Lebesgue measure on the horizon. A sequence of integrands that is Cauchy
for that energy therefore has an `L²`-limit, and the pointwise `limsup` of an almost everywhere
convergent subsequence is a representative of that limit which is again progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indicator_Icc {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ
      fun ω s => Set.indicator (Set.Icc (0 : ℝ) T) (H ω) s := by sorry
