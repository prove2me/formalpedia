-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_mul_stochasticIntegral_eq_zero
-- name    : LevyStochCalc.Brownian.Ito.integral_mul_stochasticIntegral_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:32:30.431055+00:00
-- url     : https://prove2.me/theorems/91546c8f-4dcd-408d-84cf-b57927bd9eb2
-- title:
--   integral mul stochasticIntegral eq zero
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_mul_stochasticIntegral_eq_zero` is extracted from `LevyStochCalc.Brownian.PRPPerpBridge`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_LevyStochCalc_Brownian_PRPMultidimRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From horizon orthogonality to orthogonality against every Itô integral

A weight orthogonal to the Itô integrals of integrands supported in `[0, T]` is orthogonal to
`∫_0^t K dW` for every admissible `K` and every `t > 0`. For `t ≤ T` this is because `K` clipped
to `(0, t]` is such an integrand and its integral over the horizon is `∫_0^t K dW`; for `t > T`
the remaining increment is a martingale increment after `T`, which a weight measurable before `T`
does not see.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Brownian.Ito.integral_mul_stochasticIntegral_eq_zero (V : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration V ℱ) {T : ℝ} (hT : 0 < T) {z : Ω → ℝ} (hz2 : MemLp z 2 P)
    (hzm : AEStronglyMeasurable[ℱ T] z P)
    (hperp : ∀ G : HorizonIntegrand P ℱ T, ∫ ω, z ω * G.integral V hℱ ω ∂P = 0)
    (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, z ω * stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω ∂P = 0 := by sorry
