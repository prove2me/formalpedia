-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_pow_four_le
-- name    : LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:08:28.754234+00:00
-- url     : https://prove2.me/theorems/4c23b352-2a5a-44c7-a1ef-1ddae8fb014a
-- title:
--   lintegral stochasticIntegralBrownian pow four le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le` is extracted from `LevyStochCalc.Brownian.ItoFourthMomentLintegral`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Fourth moment of the `L²` Itô integral

Truncation of a simple integrand and the `lintegral` form of the fourth-moment bound. Clamping
the coefficients to `[-C, C]` (`SimplePredictable.truncate`) moves a value no further from a
target already in `[-C, C]`, so a truncated approximant is still an approximant; the bound for
the simple integrands then passes to the `L²` Itô integral of any integrand bounded by `C` by
Fatou along an almost-everywhere convergent subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section LintegralForm

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * T ^ 2) := by sorry
