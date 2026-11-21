-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_mul_cross_increment_eq_zero
-- name    : LevyStochCalc.Brownian.Ito.integral_mul_cross_increment_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:26:50.011606+00:00
-- url     : https://prove2.me/theorems/86f9bff5-f56f-4b5a-99c0-4fd90793d3c9
-- title:
--   integral mul cross increment eq zero
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_mul_cross_increment_eq_zero` is extracted from `LevyStochCalc.Brownian.CrossVariation`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossVariation_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cross-variation of Itô integrals against distinct coordinates

A coefficient measurable at the left endpoint of a cell, carried on that cell, is a simple
integrand, so multiplying an increment of an Itô integral by such a coefficient is again an Itô
integral. The product of increments against two distinct Brownian coordinates therefore pairs to
zero against every weight known at the left endpoint, which is to say it is conditionally
centred there.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section TwoCell

end TwoCell

section PullOut

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end PullOut

section Cross

open LevyStochCalc.Brownian.Multidim

variable {d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

theorem _root_.LevyStochCalc.Brownian.Ito.integral_mul_cross_increment_eq_zero {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {Z : Ω → ℝ} (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZa : StronglyMeasurable[ℱ a] Z) :
    ∫ ω, Z ω * ((stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)) ∂P = 0 := by sorry
