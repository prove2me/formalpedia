-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_nnnorm_sum_sq_le_card_mul_sum_lintegral_nnnorm_sq
-- name    : LevyStochCalc.Ito.Picard.lintegral_nnnorm_sum_sq_le_card_mul_sum_lintegral_nnnorm_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:36:45.718961+00:00
-- url     : https://prove2.me/theorems/ce1fb8c8-e3f1-4c28-917d-ffd041894720
-- title:
--   lintegral nnnorm sum sq le card mul sum lintegral nnnorm sq
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_nnnorm_sum_sq_le_card_mul_sum_lintegral_nnnorm_sq` is extracted from `LevyStochCalc.Ito.PicardStochasticLipschitz`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardStochasticLipschitz_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Lipschitz estimates for the stochastic components of the Picard map

The `L²`-isometry `𝔼|∫_0^T H₁ dW - ∫_0^T H₂ dW|² = 𝔼 ∫_0^T |H₁ - H₂|² ds` for the difference of
two Brownian Itô integrals, the discrete Cauchy-Schwarz inequality and the `ℝ≥0∞` norm-square
identities it is combined with, and the resulting per-component `L²` Lipschitz bounds for the
diffusion and the jump component of the Picard map in terms of the Lipschitz constants of `σ` and
`γ`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

variable {Ω : Type*} [MeasurableSpace Ω]

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace E] in

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_nnnorm_sum_sq_le_card_mul_sum_lintegral_nnnorm_sq
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {d : ℕ} (M : Fin d → Ω → ℝ)
    (hM : ∀ j : Fin d, Measurable (M j)) :
    ∫⁻ ω, (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by sorry
