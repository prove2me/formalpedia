-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_integralAgainst
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:48:57.203395+00:00
-- url     : https://prove2.me/theorems/6d91ba29-bff4-40d0-8362-784b32b749d8
-- title:
--   stochasticIntegralBrownian integralAgainst
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst` is extracted from `LevyStochCalc.Brownian.ItoAlgebraAssociativity`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Associativity and locality of the `L²` Brownian Itô integral

Summing the increments of the `L²` Itô integral of a process `H` against the coefficients of a
simple integrand `G` gives the `L²` Itô integral of the product `G · H`; specialising to the step
integrands `1_{(a, b]}` identifies the `L²` Itô integral of an integrand restricted to `(a, b]`
with the increment of the integral of the unrestricted integrand across `(a, b]`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Associativity

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst {t : ℝ} (ht : 0 < t) :
    G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
        hmm hmp hmq t := by sorry
