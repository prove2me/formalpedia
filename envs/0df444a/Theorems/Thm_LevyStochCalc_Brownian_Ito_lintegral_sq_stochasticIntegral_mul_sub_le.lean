-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_stochasticIntegral_mul_sub_le
-- name    : LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:16:54.694799+00:00
-- url     : https://prove2.me/theorems/8d4c92b9-639d-4696-8a82-688ce9b7ea85
-- title:
--   lintegral sq stochasticIntegral mul sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le` is extracted from `LevyStochCalc.Brownian.ItoRiemannIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoRiemannIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Riemann sums of the Itô integral against a step weight

Summing the increments of the `L²` Itô integral of `H` across the cells of a partition, weighted
by coefficients frozen at the left endpoints, gives the `L²` Itô integral of the product of the
step weight with `H`; and replacing the step weight by a general integrand costs, in `L²`, the
`L²` distance between them times the bound on `H`.

## Main statements

* `LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst_eq_sum` — past the last
  partition point the elementary integral against a process is the plain weighted sum of its
  increments.
* `LevyStochCalc.Brownian.Ito.sum_xi_mul_stochasticIntegral_sub_ae` — that sum is the `L²` Itô
  integral of the product.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le` — the `L²` distance
  between the two products is controlled by the `L²` distance between the weights.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Riemann

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

end Riemann

section Comparison

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le
    (u v : Ω → ℝ → ℝ)
    (hmu : Measurable (Function.uncurry fun ω s => u ω s * H ω s))
    (hpu : Probability.ProgressivelyMeasurable ℱ fun ω s => u ω s * H ω s)
    (hqu : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖u ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmv : Measurable (Function.uncurry fun ω s => v ω s * H ω s))
    (hpv : Probability.ProgressivelyMeasurable ℱ fun ω s => v ω s * H ω s)
    (hqv : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖v ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => u ω s * H ω s) hmu hpu hqu T ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => v ω s * H ω s) hmv hpv hqv T ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
