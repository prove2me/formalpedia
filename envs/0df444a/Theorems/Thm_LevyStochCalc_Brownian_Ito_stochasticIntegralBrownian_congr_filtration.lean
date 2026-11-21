-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_congr_filtration
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:29:03.947782+00:00
-- url     : https://prove2.me/theorems/cd2be3f9-31c4-4c78-bbad-0c1ce341b55c
-- title:
--   stochasticIntegralBrownian congr filtration
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration` is extracted from `LevyStochCalc.Brownian.ItoFiltrationChange`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The stochastic integrals under a change of filtration

The `L²` Brownian Itô integral and the `L²` Itô–Lévy integral against a compensated Poisson
random measure are each assembled from an approximating sequence of elementary integrands
selected relative to a filtration, so one integrand integrated against one driver over two
filtrations gives two constructions. The elementary integral of such an approximant mentions no
filtration, and the `L²` distance between two elementary integrals, or between an elementary
integral and the limit, is the energy of the difference of the integrands; both constructions
are therefore the `L²`-limit of a single sequence, and they agree almost everywhere. Passing to
the augmented filtration is the case of interest, since that filtration satisfies the usual
conditions.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration` — the Brownian
  integral over `ℱ` agrees almost everywhere with the integral over a larger filtration.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_augFiltration` — the Brownian integral
  over `ℱ` agrees almost everywhere with the integral over `augFiltration ℱ P`.
* `LevyStochCalc.Poisson.Compensated.process_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_augFiltration` — the same three
  statements for the compensated Poisson integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) (h𝒢 : IsBrownianFiltration W 𝒢)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hp' : Probability.ProgressivelyMeasurable 𝒢 H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ H hm hp hq T
      =ᵐ[P] stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T := by sorry
