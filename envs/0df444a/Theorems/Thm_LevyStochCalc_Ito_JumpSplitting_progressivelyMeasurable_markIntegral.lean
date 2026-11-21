-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_progressivelyMeasurable_markIntegral
-- name    : LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_markIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:37:04.491037+00:00
-- url     : https://prove2.me/theorems/dbbe2631-5431-41dd-9492-dae805f21091
-- title:
--   progressivelyMeasurable markIntegral
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_markIntegral` is extracted from `LevyStochCalc.Ito.JumpSplitting`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplitting_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Finite-activity splitting of a jump diffusion

A jump diffusion whose jump coefficient is carried by a mark set of finite intensity is the sum
of a vector Itô process and a pathwise jump sum. The compensated Poisson integral of such a
coefficient is the pathwise integral against the random measure minus the integral against the
reference intensity, and the latter is an absolutely continuous drift, so it can be absorbed into
the drift of the Itô part.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.jumpSum` — the pathwise sum of the jumps carried by a mark set
  over a time window.
* `LevyStochCalc.Ito.JumpSplitting.continuousDrift` — the drift of a jump diffusion with the jump
  compensator subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum` — at every nonnegative time a
  jump diffusion is almost surely the sum of the vector Itô process with diffusion `σ` and drift
  `continuousDrift`, and the pathwise jump sum.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section ENNRealAux

end ENNRealAux

section Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

end Comparison

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Regularity

variable (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (i : Fin n)

theorem _root_.LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_markIntegral (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {φ : Ω → ℝ → E → ℝ} (h : Probability.MarkedProgressivelyMeasurable ℱ φ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => ∫ e in A, φ ω s e ∂ν := by sorry
