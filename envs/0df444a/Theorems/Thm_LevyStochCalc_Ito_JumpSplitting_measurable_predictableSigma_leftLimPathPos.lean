-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_measurable_predictableSigma_leftLimPathPos
-- name    : LevyStochCalc.Ito.JumpSplitting.measurable_predictableSigma_leftLimPathPos
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:02:55.354639+00:00
-- url     : https://prove2.me/theorems/7a73b6fd-ba36-4f05-af71-b0bf4d164793
-- title:
--   measurable predictableSigma leftLimPathPos
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.measurable_predictableSigma_leftLimPathPos` is extracted from `LevyStochCalc.Ito.JumpCoefficientPredictableLeftLim`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump coefficient read at the left limits of the path

The left limits of a path are the limit along a dyadic grid of the path itself, so for a path
having left limits at the positive times they are known at the current time whenever the path is
adapted and they are left-continuous there; cut to the positive times they are predictable, hence
the jump coefficient of a jump diffusion evaluated at them is predictable on the time–mark space.

## References

* Protter, *Stochastic Integration and Differential Equations*, 2005, §III.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpSplitting.measurable_predictableSigma_leftLimPathPos (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ i : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 L)) :
    Measurable[predictableSigma ℱ] fun p : ℝ × Ω => leftLimPathPos X p.1 p.2 := by sorry
