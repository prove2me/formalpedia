-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_integral_mul_charCompensator
-- name    : LevyStochCalc.Poisson.integral_mul_charCompensator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:06:00.343485+00:00
-- url     : https://prove2.me/theorems/b01e1c05-ae2f-41f9-a581-48591ca9ce8c
-- title:
--   integral mul charCompensator
-- statement:
--   The source theorem `LevyStochCalc.Poisson.integral_mul_charCompensator` is extracted from `LevyStochCalc.Poisson.CharacterFubini`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterFubini_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the compensator as a time integral of the pairings with the characters

The chain rule's integrand for the family cut at `t` factors as a deterministic mark times the
predictable exponential. Pairing a weight with the compensator and swapping the two integrals
therefore leaves, at each point of the window, the mark times the pairing of the weight with the
character at that time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Fubini

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.LevyStochCalc.Poisson.integral_mul_charCompensator (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {r : Ω → ℝ} (hr1 : Integrable r P) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {t : ℝ} (htT : t ≤ T) :
    ∫ ω, (r ω : ℂ) * charCompensator N w Bfam A T t ω ∂P
      = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          charMark w Bfam t q * ∫ ω, (r ω : ℂ) * charAt N w Bfam q.1 ω ∂P
          ∂(referenceIntensity ν) := by sorry
