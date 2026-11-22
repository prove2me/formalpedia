-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_markedProgressivelyMeasurable_add
-- name    : LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:23:12.394841+00:00
-- url     : https://prove2.me/theorems/7eb301ff-c3a7-4d30-b4ce-200550fa599f
-- title:
--   markedProgressivelyMeasurable add
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_add` is extracted from `LevyStochCalc.Poisson.CompensatedRange`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the compensated Poisson integral on a horizon

A marked integrand supported in `[0, T]`, jointly and progressively measurable and of finite
energy, is admissible for the compensated integral up to `T`. Such integrands are closed under
sums and scalar multiples, and the integral is additive and homogeneous on them, so their
integrals form a submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence
of integrands to an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Progressive

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_add {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (h₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (h₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => φ₁ ω s e + φ₂ ω s e := by sorry
