-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_integral_mul_integral_eq_zero
-- name    : LevyStochCalc.Poisson.Compensated.integral_mul_integral_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:44:59.652282+00:00
-- url     : https://prove2.me/theorems/c9aadc80-45ba-4772-a9d5-70ef6283d612
-- title:
--   integral mul integral eq zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.integral_mul_integral_eq_zero` is extracted from `LevyStochCalc.Poisson.PerpBridge`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The perp bridge for the compensated integral

A weight measurable before a horizon does not see the compensated integral beyond it: the
increment is a martingale increment, and conditioning on the horizon kills it. So orthogonality
to every admissible integrand over `[0, T]` extends to every admissible integrand over any
larger horizon. This is the marked counterpart of the Brownian perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Congr

end Congr

section Clip

namespace MarkedHorizonIntegrand

end MarkedHorizonIntegrand

end Clip

section Bridge

theorem _root_.LevyStochCalc.Poisson.Compensated.integral_mul_integral_eq_zero (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {z : Ω → ℝ} (hz2 : MemLp z 2 P)
    (hzm : AEStronglyMeasurable[ℱ T] z P)
    (hperp : ∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, z ω * G.integral N hℱ ω ∂P = 0)
    {R : ℝ} (hTR : T ≤ R) (G : MarkedHorizonIntegrand P ν ℱ R) :
    ∫ ω, z ω * G.integral N hℱ ω ∂P = 0 := by sorry
