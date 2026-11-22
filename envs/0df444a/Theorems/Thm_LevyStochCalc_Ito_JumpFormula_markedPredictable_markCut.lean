-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_markedPredictable_markCut
-- name    : LevyStochCalc.Ito.JumpFormula.markedPredictable_markCut
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:56:44.366889+00:00
-- url     : https://prove2.me/theorems/79e9888f-364c-4cfb-8ab6-a465ca92d46b
-- title:
--   markedPredictable markCut
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.markedPredictable_markCut` is extracted from `LevyStochCalc.Ito.JumpFormulaClosure`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaClosure_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exhausting a σ-finite mark space by finite-activity complements

A σ-finite intensity has a monotone family of measurable sets of finite measure covering the mark
space, so the complements of that family are antitone, have empty intersection, and carry finite
intensity on their own complements. Truncating a jump coefficient to the complement of a member
therefore leaves finite activity, and the members shrink to a null set.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.smallMarks` — the complements of a spanning family of the
  intensity.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurableSet_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.antitone_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.measure_compl_smallMarks_lt_top`,
  `LevyStochCalc.Ito.JumpFormula.iInter_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.measure_iInter_smallMarks` — the four properties the small-jump
  truncation asks of a family of mark sets.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe v

variable {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]

section Augmentation

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

end Augmentation

section Repair

universe w

variable {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}

end Repair

section MarkCut

open LevyStochCalc.Probability

universe u₃ v₃

variable {Ω : Type u₃} [MeasurableSpace Ω] {E : Type v₃} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Ito.JumpFormula.markedPredictable_markCut {φ : Ω → ℝ → E → ℝ} (hφ : MarkedPredictable ℱ ν φ)
    (hφ0 : ∀ (ω : Ω) (s : ℝ) (e : E), s ≤ 0 → φ ω s e = 0)
    {A : Set E} (hA : MeasurableSet A) :
    MarkedPredictable ℱ ν (LevyStochCalc.Poisson.Compensated.markCut A φ) := by sorry
