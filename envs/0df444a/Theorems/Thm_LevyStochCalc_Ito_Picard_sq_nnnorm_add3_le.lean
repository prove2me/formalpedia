-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_sq_nnnorm_add3_le
-- name    : LevyStochCalc.Ito.Picard.sq_nnnorm_add3_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T21:22:00.968768+00:00
-- url     : https://prove2.me/theorems/fb1efb95-5c13-403f-8d64-99033b26143f
-- title:
--   sq nnnorm add3 le
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.sq_nnnorm_add3_le` is extracted from `LevyStochCalc.Ito.PicardOutputMoments`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F001

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

theorem _root_.LevyStochCalc.Ito.Picard.sq_nnnorm_add3_le (x y z : ℝ) :
    (‖x + y + z‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by sorry
