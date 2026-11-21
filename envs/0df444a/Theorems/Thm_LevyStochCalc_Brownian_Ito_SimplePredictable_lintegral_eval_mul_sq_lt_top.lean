-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_eval_mul_sq_lt_top
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_eval_mul_sq_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T17:34:14.203713+00:00
-- url     : https://prove2.me/theorems/88a3815a-f854-4014-8851-1149a0ec5078
-- title:
--   lintegral eval mul sq lt top
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_eval_mul_sq_lt_top` is extracted from `LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple integrands as integrands of the `L²` Brownian Itô integral

A simple integrand is uniformly bounded in both variables, jointly measurable, square-integrable
on every time window and, when its coefficients are adapted to a filtration, progressively
measurable, so it is an admissible integrand for the `L²` Itô integral in its own right; the two
elementary integrals of adapted simple integrands obey the Itô isometry for their difference at
an intermediate time, and the `L²` Itô integral of a simple integrand agrees almost everywhere
with its elementary integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_eval_mul_sq_lt_top {T : ℝ} (G : SimplePredictable Ω T)
    {P : Measure Ω} [IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T' : ℝ) (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
