-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_integral_mul_increment_eq_zero
-- name    : LevyStochCalc.Poisson.Compensated.integral_mul_increment_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:47:07.949471+00:00
-- url     : https://prove2.me/theorems/0836cc5b-e4d3-4986-bd32-81aabf43621d
-- title:
--   integral mul increment eq zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.integral_mul_increment_eq_zero` is extracted from `LevyStochCalc.Poisson.PerpBridge`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PerpBridge_F000

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

theorem _root_.LevyStochCalc.Poisson.Compensated.integral_mul_increment_eq_zero (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {z : Ω → ℝ} (hz2 : MemLp z 2 P) {T t : ℝ}
    (hzm : AEStronglyMeasurable[ℱ T] z P) (hTt : T ≤ t) :
    ∫ ω, z ω * (stochasticIntegral N ℱ hℱ φ hm hp hq t ω
      - stochasticIntegral N ℱ hℱ φ hm hp hq T ω) ∂P = 0 := by sorry
