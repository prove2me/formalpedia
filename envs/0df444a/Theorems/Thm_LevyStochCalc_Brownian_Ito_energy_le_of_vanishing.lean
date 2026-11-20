-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_energy_le_of_vanishing
-- name    : LevyStochCalc.Brownian.Ito.energy_le_of_vanishing
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:14:40.083308+00:00
-- url     : https://prove2.me/theorems/66c1d778-7d1c-4525-8717-30c8e9d6a298
-- title:
--   energy le of vanishing
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.energy_le_of_vanishing` is extracted from `LevyStochCalc.Brownian.ItoIntegrandComplete`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F000

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

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.energy_le_of_vanishing {H : Ω → ℝ → ℝ} {T : ℝ}
    (hz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → H ω s = 0) (T' : ℝ) :
    energy P T' H ≤ energy P T H := by sorry
