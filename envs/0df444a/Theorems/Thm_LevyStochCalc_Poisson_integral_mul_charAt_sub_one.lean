-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_integral_mul_charAt_sub_one
-- name    : LevyStochCalc.Poisson.integral_mul_charAt_sub_one
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:50:24.959892+00:00
-- url     : https://prove2.me/theorems/9fa2c5a9-f437-4b89-b890-8b06e8be4599
-- title:
--   integral mul charAt sub one
-- statement:
--   The source theorem `LevyStochCalc.Poisson.integral_mul_charAt_sub_one` is extracted from `LevyStochCalc.Poisson.CharacterCompensator`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterCompensator_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality removes the compensated integrals from the character's increment

For a square-integrable weight orthogonal to every compensated integral over the horizon, the
pairing with the character's increment `χ_t − 1` reduces to the pairing with the compensator: the
two compensated halves of the jump chain rule integrate to zero against the weight.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Compensator

theorem _root_.LevyStochCalc.Poisson.integral_mul_charAt_sub_one (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    {t : ℝ} (htT : t ≤ T) :
    ∫ ω, (r ω : ℂ) * (charAt N w Bfam t ω - 1) ∂P
      = ∫ ω, (r ω : ℂ) * charCompensator N w Bfam A T t ω ∂P := by sorry
