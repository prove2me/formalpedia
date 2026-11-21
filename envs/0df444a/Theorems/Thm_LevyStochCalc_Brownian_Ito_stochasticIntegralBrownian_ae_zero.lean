-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_ae_zero
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:15:04.257044+00:00
-- url     : https://prove2.me/theorems/6d8fae80-af0e-4145-bd1a-195f48d47336
-- title:
--   stochasticIntegralBrownian ae zero
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero` is extracted from `LevyStochCalc.Brownian.ItoZero`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoZero_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô integral of the zero integrand

The `L²`-isometry forces the Itô integral of the zero integrand to vanish almost surely, at
every time. This is what lets a coordinate of a vector Itô process carry no diffusion.

## Main statements

* `LevyStochCalc.Probability.progressivelyMeasurable_const` — a constant process is
  progressively measurable.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero` — the Itô integral of the zero
  integrand vanishes almost surely.
-/

namespace LevyStochCalc

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero
    (hm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)))
    (hp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ))
    (hq : ∀ T, 0 < T → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq t =ᵐ[P] 0 := by sorry
