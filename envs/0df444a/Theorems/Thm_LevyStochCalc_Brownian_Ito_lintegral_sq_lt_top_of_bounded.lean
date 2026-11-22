-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_lt_top_of_bounded
-- name    : LevyStochCalc.Brownian.Ito.lintegral_sq_lt_top_of_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:43:13.497225+00:00
-- url     : https://prove2.me/theorems/e462ae02-705b-4f68-bf28-958f85374b39
-- title:
--   lintegral sq lt top of bounded
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_lt_top_of_bounded` is extracted from `LevyStochCalc.Brownian.ItoTrigIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_ScaledTrig_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for the scaled cosine and sine of a Brownian increment

`x ↦ cos (l * x)` and `x ↦ sin (l * x)` satisfy the hypotheses of Itô's formula for a scalar Itô
process, so for a version of `∫ 1_{(a,b]} dW` they give

  `cos (l * X_T) − cos (l * X_0) = ∫ (−l sin (l X)) 1_{(a,b]} dW − (l²/2) ∫ cos (l X) 1_{(a,b]} ds`

and the companion identity for the sine.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_sq_lt_top_of_bounded {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → ℝ → ℝ} {M : ℝ} (hM : ∀ ω s, |F ω s| ≤ M) (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
