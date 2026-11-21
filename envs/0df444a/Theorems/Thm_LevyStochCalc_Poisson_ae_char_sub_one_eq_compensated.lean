-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_ae_char_sub_one_eq_compensated
-- name    : LevyStochCalc.Poisson.ae_char_sub_one_eq_compensated
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:36:58.01859+00:00
-- url     : https://prove2.me/theorems/0a200f66-eacf-4a97-8179-790b9dd19db3
-- title:
--   ae char sub one eq compensated
-- statement:
--   The source theorem `LevyStochCalc.Poisson.ae_char_sub_one_eq_compensated` is extracted from `LevyStochCalc.Poisson.CharacterIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Theorems.Thm_LevyStochCalc_Probability_MarkedPredictable_markedProgressivelyMeasurable
import Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F002
import Definitions.Def_SourceProof_6bebe70af91e345e56c64c09

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable integrand of the jump chain rule

For a simple integrand carried by a window of finite mark measure the integrand of the jump chain
rule has an exact predictable form: the strictly-past window sum is replaced by its predictable
representative and the deterministic factors are predictable because they are carried by the
window. The integrand is bounded by twice the indicator of the window, so its real and imaginary
parts are admissible for the compensated integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Integrand

variable (N : PoissonRandomMeasure P ν)

end Integrand

section Assembly

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Poisson.ae_char_sub_one_eq_compensated (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hT : 0 < T) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    ∀ᵐ ω ∂P,
      Complex.exp (Complex.I * (windowSum N (⋃ j, Bfam j) (simpleMark w Bfam) T ω : ℂ)) - 1
        = ((Compensated.process N ℱ hℱ (charRe N w Bfam A T)
              (measurable_charRe N hℱ w hBm hA hAν hBsub)
              (markedPredictable_charRe N hℱ w hBm hA hAν hBsub).markedProgressivelyMeasurable
              (fun T' _ => sq_charRe N w hA hAν hBsub T') T ω : ℝ) : ℂ)
          + ((Compensated.process N ℱ hℱ (charIm N w Bfam A T)
              (measurable_charIm N hℱ w hBm hA hAν hBsub)
              (markedPredictable_charIm N hℱ w hBm hA hAν hBsub).markedProgressivelyMeasurable
              (fun T' _ => sq_charIm N w hA hAν hBsub T') T ω : ℝ) : ℂ) * Complex.I
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
              charIntegrand N w Bfam A T ω q.1 q.2 ∂(referenceIntensity ν) := by sorry
