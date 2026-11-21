-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_integral_compensatedProfile_mul
-- name    : LevyStochCalc.Poisson.integral_compensatedProfile_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T16:38:38.097915+00:00
-- url     : https://prove2.me/theorems/f9c5c8b1-bef0-464f-88f8-e9b926f2ae1c
-- title:
--   integral compensatedProfile mul
-- statement:
--   The source theorem `LevyStochCalc.Poisson.integral_compensatedProfile_mul` is extracted from `LevyStochCalc.Poisson.CompensatedProfileMoments`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# First and second moments of the compensated integral of a mark profile

The compensated integral of a simple mark profile over a step is a linear combination of
compensated counts, each of mean zero, and the `L²(P)` pairing of two such integrals over a
common step is the step length times the `L²(ν)` pairing of their mark functions. Both
identities pass to the `L²` limits that define the compensated integral of a square-integrable
mark profile: over the step `(a, b]` the mean of `J(f)` vanishes and

  `E[J(f) J(g)] = (b − a) ∫ f g dν`,   `E[J(f)²] = (b − a) ∫ f² dν`.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral` — the mean of the compensated
  step integral of a simple mark profile.
* `LevyStochCalc.Poisson.integral_compensatedProfile` — the mean of the compensated integral of
  a square-integrable mark profile over a step.
* `LevyStochCalc.Poisson.integral_compensatedProfile_mul` — the `L²(P)` pairing of the
  compensated integrals of two square-integrable mark profiles over a common step.
* `LevyStochCalc.Poisson.integral_compensatedProfile_sq` — the second moment of the compensated
  integral of a square-integrable mark profile over a step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Passing an `L²` pairing to the limit -/

/-! ### The mean -/

/-! ### The second moments -/

theorem _root_.LevyStochCalc.Poisson.integral_compensatedProfile_mul (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProfile N f a b ω * compensatedProfile N g a b ω ∂P
      = (b - a) * ∫ e, f e * g e ∂ν := by sorry
