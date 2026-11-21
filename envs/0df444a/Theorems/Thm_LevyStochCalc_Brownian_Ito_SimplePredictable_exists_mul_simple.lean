-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_exists_mul_simple
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:46:03.817039+00:00
-- url     : https://prove2.me/theorems/19d54fdd-e74b-40e4-a0a9-4c208727d5be
-- title:
--   exists mul simple
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple` is extracted from `LevyStochCalc.Brownian.ItoAlgebraProduct`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section SimpleVsGeneral

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end SimpleVsGeneral

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T₁ T₂ : ℝ} (G : SimplePredictable Ω T₁) (K : SimplePredictable Ω T₂)
    (h_adaptG : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    (h_adaptK : ∀ i : Fin K.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (K.partition i.castSucc)) (K.ξ i)) :
    ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = G.eval s ω * K.eval s ω)
      ∧ (∀ t ω, G.integralAgainst (fun u ω' => simpleIntegral W K u ω') t ω
          = simpleIntegral W Q t ω) := by sorry
