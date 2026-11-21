-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_add
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:26:26.343353+00:00
-- url     : https://prove2.me/theorems/115cfbf0-61ef-4671-a716-11e44d271ef9
-- title:
--   stochasticIntegralBrownian add
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add` is extracted from `LevyStochCalc.Brownian.ItoLinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Additivity of the L² Itô integral in the integrand

The Itô isometry and the isometry of differences determine every squared `L²`-distance among
`∫ H₁ dW`, `∫ H₂ dW` and `∫ (H₁ + H₂) dW` in terms of the energies of `H₁`, `H₂`, `H₁ + H₂` and
`H₁ − H₂`. The parallelogram law for those energies then forces
`∫ (H₁ + H₂) dW = ∫ H₁ dW + ∫ H₂ dW` almost everywhere.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Energy

variable {H₁ H₂ : Ω → ℝ → ℝ}

end Energy

section Parallelogram

end Parallelogram

section Additivity

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
    (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
    (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa T
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
        + stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω := by sorry
