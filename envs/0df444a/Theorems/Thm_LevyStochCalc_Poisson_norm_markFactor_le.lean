-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_norm_markFactor_le
-- name    : LevyStochCalc.Poisson.norm_markFactor_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:06:04.776691+00:00
-- url     : https://prove2.me/theorems/441c9411-a460-4032-8759-bc3ca7ba9abc
-- title:
--   norm markFactor le
-- statement:
--   The source theorem `LevyStochCalc.Poisson.norm_markFactor_le` is extracted from `LevyStochCalc.Poisson.CharacterMarkFactor`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterMarkFactor_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The deterministic mark factor of the chain rule's integrand

At each time and mark the chain rule's integrand is the product of a deterministic factor,
carrying the indicator of the family and the jump `e^{i m} - 1` that a point there contributes,
with the exponential of the strict past. Inside the window the second factor agrees almost
surely with the character at that time, and so does the predictable representative of the
strict-past character.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section MarkFactor

variable (N : PoissonRandomMeasure P ν)

omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] in

theorem _root_.LevyStochCalc.Poisson.norm_markFactor_le (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (q : ℝ × E) :
    ‖markFactor w Bfam q‖ ≤ 2 := by sorry
