-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_isometry_diff_stochasticIntegralBrownian
-- name    : LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:31:01.051047+00:00
-- url     : https://prove2.me/theorems/ae09d7a3-a3cf-4da6-897b-2127dec8480c
-- title:
--   isometry diff stochasticIntegralBrownian
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionApi`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the `stochasticIntegral` API

The martingale property of the compensated square for the right-continuation `ℱ₊` of `ℱ`,
the unified existence theorem `itoIsometry_brownian_unified_existence` combining the
martingale, quadratic-variation and isometry conclusions, the isometry for differences of
integrands, and the `stochasticIntegral` interface with `itoIsometry`,
`quadVar_stochasticIntegral` and `martingale_stochasticIntegral`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end MasterSequence

theorem _root_.LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) (H₁ H₂ : Ω → ℝ → ℝ)
    (h_meas₁ : Measurable (Function.uncurry H₁)) (h_meas₂ : Measurable (Function.uncurry H₂))
    (h_progMeas₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (h_progMeas₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (h_sq₁ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_sq₂ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ T ω
        - stochasticIntegralBrownian W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
