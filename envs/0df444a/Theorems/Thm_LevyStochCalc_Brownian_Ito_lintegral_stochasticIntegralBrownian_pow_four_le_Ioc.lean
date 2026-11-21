-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_pow_four_le_Ioc
-- name    : LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:14:10.692663+00:00
-- url     : https://prove2.me/theorems/ba82986d-d498-4665-a814-ab514d6d0b87
-- title:
--   lintegral stochasticIntegralBrownian pow four le Ioc
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc` is extracted from `LevyStochCalc.Brownian.ItoIncrementMomentBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of an increment of the Itô integral

The fourth moment of `∫_a^b H dW` for an integrand bounded by `C` is at most
`(6 + c)·C⁴·(b − a)²`, with `c` the fourth moment of the standard Gaussian, the second moment is
at most `C²·(b − a)`, and interpolating between the two by `2λ|y|³ ≤ λ²y² + y⁴` at `λ = √(b − a)`
bounds the third absolute moment. The fourth-moment bound is the per-tile variance budget of
`LevyStochCalc.Brownian.Ito.SimplePredictable.varClock` applied to simple approximants of
`1_{(a, b]}·H` that themselves vanish off `(a, b]`.

## Main statements

* `lintegral_stochasticIntegralBrownian_pow_four_le_Ioc` — the fourth-moment bound for an
  integrand supported in `(a, b]`.
* `lintegral_stochasticIntegralBrownian_sub_pow_four_le` —
  `𝔼|∫_a^b H dW|⁴ ≤ (6 + c)·C⁴·(b − a)²` for an integrand bounded by `C`.
* `lintegral_stochasticIntegralBrownian_sub_sq_le` — `𝔼|∫_a^b H dW|² ≤ C²·(b − a)`.
* `integral_abs_sub_pow_three_le` —
  `𝔼|∫_a^b H dW|³ ≤ ((C² + (6 + c)C⁴)/2)·(b − a)·√(b − a)`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section IncrementBound

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc
    (F : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry F))
    (hp : Probability.ProgressivelyMeasurable ℱ F)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ ω s, |F ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ ω s, s ∉ Set.Ioc a b → F ω s = 0) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by sorry
