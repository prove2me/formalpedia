-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkStep_integral_mul_at
-- name    : LevyStochCalc.Poisson.Compensated.MarkStep.integral_mul_at
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:37:06.038304+00:00
-- url     : https://prove2.me/theorems/6f63bb81-4b1d-429b-915b-58080eb4d4e7
-- title:
--   integral mul at
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_mul_at` is extracted from `LevyStochCalc.Poisson.MarkStepPolarised`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepPolarised_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The bilinear form of the `L²` isometry for mark-step integrands

For two adapted mark-step integrands `G, G'` on a common time grid, the expectation of the
product of their compensated integrals up to a time `t ≥ 0` is the expectation of the time-mark
integral of the product of the integrands,
`E[(∫_0^t ∫_E G dÑ)(∫_0^t ∫_E G' dÑ)] = E[∫_E ∫_0^t G(s, e) G'(s, e) ds ν(de)]`, and the same
identity holds for the integrals over the whole horizon. It comes from the isometry for a
difference applied to the pairs `G, G'` and `G, G'.neg`, together with the polarisation identity
`4 a a' = (a + a') ^ 2 - (a - a') ^ 2`. Splitting the nested integral of that identity into its
two halves uses the boundedness of a mark-step integrand and the finite intensity of its mark
sets.

## Main statements

* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_mul_at` — the bilinear identity up to a
  time `t ≥ 0`.
* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_full_mul` — the bilinear identity for the
  integrals over the whole horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Polarisation

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (hℱ : IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkStep.integral_mul_at (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, G.integral N t ω * G'.integral N t ω ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
          G.eval s e ω * G'.eval s e ω ∂volume ∂ν) ∂P := by sorry
