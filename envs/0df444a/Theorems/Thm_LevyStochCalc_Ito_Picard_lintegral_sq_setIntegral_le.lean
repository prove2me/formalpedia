-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_setIntegral_le
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:16:12.217312+00:00
-- url     : https://prove2.me/theorems/8212b335-4bde-4bce-99eb-25bd10e76102
-- title:
--   lintegral sq setIntegral le
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le` is extracted from `LevyStochCalc.Ito.PicardOutputMoments`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the Picard step

Each of the three components of the Picard step — the Lebesgue drift integral, the Brownian
stochastic integral and the compensated jump integral — is bounded in `L²` uniformly over
`[0, T]` by the energies of its integrand, through Cauchy–Schwarz for the drift and the Itô
and Itô–Lévy isometries for the two stochastic components; summing the three bounds gives a
finite Bielecki norm for the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) {t : ℝ} (ht : 0 ≤ t)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal t
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
