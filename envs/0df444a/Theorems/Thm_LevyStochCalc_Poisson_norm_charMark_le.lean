-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_norm_charMark_le
-- name    : LevyStochCalc.Poisson.norm_charMark_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:58:41.571687+00:00
-- url     : https://prove2.me/theorems/708415d8-26d6-46b5-b8fe-f64ccd510827
-- title:
--   norm charMark le
-- statement:
--   The source theorem `LevyStochCalc.Poisson.norm_charMark_le` is extracted from `LevyStochCalc.Poisson.CharacterFubini`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterFubini_F000

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

omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem _root_.LevyStochCalc.Poisson.norm_charMark_le (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (t : ℝ) (q : ℝ × E) :
    ‖charMark w Bfam t q‖ ≤ 2 := by sorry
