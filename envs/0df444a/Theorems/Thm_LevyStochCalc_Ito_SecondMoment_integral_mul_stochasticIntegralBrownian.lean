-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_SecondMoment_integral_mul_stochasticIntegralBrownian
-- name    : LevyStochCalc.Ito.SecondMoment.integral_mul_stochasticIntegralBrownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:27:25.15918+00:00
-- url     : https://prove2.me/theorems/a7078fe4-acbe-4f43-b6b0-a35345e9257a
-- title:
--   integral mul stochasticIntegralBrownian
-- statement:
--   The source theorem `LevyStochCalc.Ito.SecondMoment.integral_mul_stochasticIntegralBrownian` is extracted from `LevyStochCalc.Ito.SecondMomentToolkit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Auxiliary lemmas for the second moment of an Itô–Lévy process

The `L²` lemmas behind the expectation form of the quadratic Itô formula: the second moment of a
square-integrable variable as the real part of its energy, the expansion of the square of a sum,
the evaluation of a square-integrable martingale paired against a variable measurable at an
earlier time, and the exchange of a time integral with a pairing. The running integral
`∫_0^s b_r dr` of a drift over a window `[0, T]` is introduced as a jointly measurable function of
the sample point and the time, together with the pathwise identities
`(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds` and, for two integrable functions,
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`; and the polarised isometry for
the Brownian integral, the expected product of two Brownian integrals at a time being the expected
time integral of the product of their integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Toolkit

end Toolkit

section Running

variable (b : ℝ → Ω → ℝ) (T : ℝ)

variable {b T}

end Running

section Polarised

theorem _root_.LevyStochCalc.Ito.SecondMoment.integral_mul_stochasticIntegralBrownian (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, H ω s * K ω s ∂volume ∂P := by sorry
