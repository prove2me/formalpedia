-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_congr_ae
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:10:04.729236+00:00
-- url     : https://prove2.me/theorems/8adc6e09-440c-49d5-904c-aa7f6d58a7f1
-- title:
--   stochasticIntegralBrownian congr ae
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_ae` is extracted from `LevyStochCalc.Brownian.ItoLocalityStrict`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Strict locality of the Itô integral

Two integrands that agree almost everywhere on a window have almost surely equal integrals
(`stochasticIntegralBrownian_congr_ae`), because the difference isometry turns the vanishing of
the energy of their difference into the vanishing of the second moment of the difference of the
integrals.

That upgrades the locality statement of `Brownian/ItoLocality.lean` from agreement at the times
`s ≤ τ ω` to agreement at the times `s < τ ω` (`stochasticIntegralBrownian_congr_of_lt`): the two
cut-off integrands then differ at the single time `s = τ ω`, a Lebesgue-null set of times. The
strict form is what a càdlàg path needs, since two integrands read along it can disagree exactly
at a jump time.

## Main statements

* `stochasticIntegralBrownian_congr_ae` — almost-everywhere equal integrands, almost surely
  equal integrals.
* `stochasticIntegralBrownian_congr_of_lt` — integrands agreeing strictly below a stopping time
  have the same integral at a time that stopping time has not reached.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_ae {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂)) (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), H₁ ω s = H₂ ω s) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T := by sorry
