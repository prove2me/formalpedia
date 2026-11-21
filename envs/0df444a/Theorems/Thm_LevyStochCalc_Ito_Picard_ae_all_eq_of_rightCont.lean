-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_ae_all_eq_of_rightCont
-- name    : LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:45:29.789901+00:00
-- url     : https://prove2.me/theorems/ad577d6e-c66b-4013-af25-5bbfafb7f20d
-- title:
--   ae all eq of rightCont
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont` is extracted from `LevyStochCalc.Ito.PicardGlobal`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F002

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

omit [MeasurableSpace E] [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont {A B : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hA : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => A s ω) (nhdsWithin t (Set.Ioi t)) (nhds (A t ω)))
    (hB : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => B s ω) (nhdsWithin t (Set.Ioi t)) (nhds (B t ω)))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, A t ω = B t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, A t ω = B t ω := by sorry
