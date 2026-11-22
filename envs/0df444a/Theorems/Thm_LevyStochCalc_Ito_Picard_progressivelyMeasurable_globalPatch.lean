-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_progressivelyMeasurable_globalPatch
-- name    : LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T07:47:35.671754+00:00
-- url     : https://prove2.me/theorems/4fd3eccb-0058-4c03-a2af-4c711ed66264
-- title:
--   progressivelyMeasurable globalPatch
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch` is extracted from `LevyStochCalc.Ito.PicardGlobal`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

/-! ### The glued path map -/

omit [MeasurableSpace E] [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => globalPatch Y s ω i := by sorry
