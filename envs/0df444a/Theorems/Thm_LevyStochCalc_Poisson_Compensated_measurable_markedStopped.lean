-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_measurable_markedStopped
-- name    : LevyStochCalc.Poisson.Compensated.measurable_markedStopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:48:36.932523+00:00
-- url     : https://prove2.me/theorems/0b9a8ec3-14cf-491b-8da4-9e02845f6b9d
-- title:
--   measurable markedStopped
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.measurable_markedStopped` is extracted from `LevyStochCalc.Ito.CompensatedLocalityCutoff`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The marked integrand cut off at a stopping time

The marked process `markedStopped τ φ`, which agrees with `φ` at the times a stopping time `τ`
has not passed and vanishes afterwards, is dominated pointwise by `φ` and inherits from it joint
measurability, marked progressive measurability and finite energy; those three admissibility
properties transport along an equality of marked integrands and are stable under differences.

## Main definitions

* `markedStopped τ φ` — the marked process `φ` cut off at the stopping time `τ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section MarkedStopped

variable (τ : Ω → WithTop ℝ) (φ : Ω → ℝ → E → ℝ)

variable {τ φ}

theorem _root_.LevyStochCalc.Poisson.Compensated.measurable_markedStopped (hτ : IsStoppingTime ℱ τ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) :
    Measurable fun p : Ω × ℝ × E => markedStopped τ φ p.1 p.2.1 p.2.2 := by sorry
