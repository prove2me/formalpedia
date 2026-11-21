-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkStep_integral_eq_sub_integral
-- name    : LevyStochCalc.Poisson.Compensated.MarkStep.integral_eq_sub_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:40:25.268791+00:00
-- url     : https://prove2.me/theorems/29241225-8c6d-457a-8e5a-f7a1dc9db74a
-- title:
--   integral eq sub integral
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_eq_sub_integral` is extracted from `LevyStochCalc.Poisson.MarkStepPathwise`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepPathwise_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-step approximants are pathwise and predictable

The approximants the compensated integral is built from are finite combinations of indicators of
time–mark rectangles with coefficients known at the left endpoint of their piece. Their integral
against any measure finite on those rectangles is the matching finite combination, so over the
whole horizon the approximant's compensated integral is the difference of its integrals against
the random measure and against the reference intensity. Adaptedness of the coefficients makes the
approximant predictable, which is what the compensator identity asks for.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P] {g : TimeGrid}

namespace MarkStep

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkStep.integral_eq_sub_integral (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (t : ℝ)
    (ω : Ω) (hfin : ∀ i (k : Fin G.K),
      N.N ω (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ≠ ⊤) :
    G.integral N t ω
      = (∫ q, (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω ∂(N.N ω))
        - ∫ q, (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω
            ∂(referenceIntensity ν) := by sorry
