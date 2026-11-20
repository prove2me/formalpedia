-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists
-- name    : LevyStochCalc.Brownian.BrownianMotion.exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:06:13.251176+00:00
-- url     : https://prove2.me/theorems/c1070e48-f6ed-4d0f-8a21-bfa2d2ab515e
-- title:
--   exists
-- statement:
--   The source theorem `LevyStochCalc.Brownian.BrownianMotion.exists` is extracted from `LevyStochCalc.Brownian.Existence`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Existence_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian motion from a pre-Brownian process

A process `X : ℝ≥0 → Ω → ℝ` with the finite-dimensional laws of Brownian motion
(`ProbabilityTheory.IsPreBrownianReal`), measurable marginals and continuous paths yields a
`BrownianMotion P` in the sense of `LevyStochCalc.Brownian.Construction`: extend to real time by
`t ↦ X (t⁺) − X 0`, which vanishes at non-positive times and is re-centred at the origin. The weak
Markov property `ProbabilityTheory.IsPreBrownianReal.indepFun_shift` supplies the σ-algebra
independence of the past from a future increment.

## Main statements

* `BrownianMotion.ofIsPreBrownianReal` — the construction.
* `BrownianMotion.exists` — existence, from the canonical Brownian motion `brownian` on
  `gaussianLimit`, lifted to an arbitrary universe.
-/

namespace LevyStochCalc.Brownian

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Brownian.BrownianMotion.exists :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (BrownianMotion P) := by sorry
