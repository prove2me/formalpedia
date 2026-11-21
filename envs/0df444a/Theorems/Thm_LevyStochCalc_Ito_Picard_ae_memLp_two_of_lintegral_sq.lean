-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_ae_memLp_two_of_lintegral_sq
-- name    : LevyStochCalc.Ito.Picard.ae_memLp_two_of_lintegral_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:26:41.185781+00:00
-- url     : https://prove2.me/theorems/173cf8b5-70b5-406b-9aa7-a07c3a9a2abc
-- title:
--   ae memLp two of lintegral sq
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.ae_memLp_two_of_lintegral_sq` is extracted from `LevyStochCalc.Ito.PicardOutputModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Càdlàg modifications of the Picard step

The `L²` stochastic integral is defined separately at each time, so the Picard step as first
written has no path regularity. Replacing each Brownian component by a càdlàg adapted
modification, and the drift by its almost surely continuous version, produces a process
indistinguishable from the step at every fixed time and càdlàg along almost every path; the
Bielecki norm is unchanged, and the result is a genuine self-map of the space of bounded
adapted càdlàg processes.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Ito.Picard.ae_memLp_two_of_lintegral_sq {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hfin : ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ b : ℝ,
      MeasureTheory.MemLp (f ω) 2 (volume.restrict (Set.Icc (0 : ℝ) b)) := by sorry
