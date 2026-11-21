-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_continuous_setIntegral_Icc_of_integrableOn
-- name    : LevyStochCalc.Ito.Picard.continuous_setIntegral_Icc_of_integrableOn
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:31:27.606732+00:00
-- url     : https://prove2.me/theorems/6734cfc8-a9fa-416d-b7a4-035fe719eafb
-- title:
--   continuous setIntegral Icc of integrableOn
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.continuous_setIntegral_Icc_of_integrableOn` is extracted from `LevyStochCalc.Ito.PicardOutputModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F000

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

theorem _root_.LevyStochCalc.Ito.Picard.continuous_setIntegral_Icc_of_integrableOn {f : ℝ → ℝ}
    (h_int : ∀ b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) b) volume) :
    Continuous fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by sorry
