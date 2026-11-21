-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_eval_simple
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:15:04.885448+00:00
-- url     : https://prove2.me/theorems/f81a959d-74e0-4d9b-b686-9c8f5894c0e6
-- title:
--   stochasticIntegralBrownian eval simple
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple` is extracted from `LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple integrands as integrands of the `L²` Brownian Itô integral

A simple integrand is uniformly bounded in both variables, jointly measurable, square-integrable
on every time window and, when its coefficients are adapted to a filtration, progressively
measurable, so it is an admissible integrand for the `L²` Itô integral in its own right; the two
elementary integrals of adapted simple integrands obey the Itô isometry for their difference at
an intermediate time, and the `L²` Itô integral of a simple integrand agrees almost everywhere
with its elementary integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section EvalSimple

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t
      =ᵐ[P] simpleIntegral W G t := by sorry
