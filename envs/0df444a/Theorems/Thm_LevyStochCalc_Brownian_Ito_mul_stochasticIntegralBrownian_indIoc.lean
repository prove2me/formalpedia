-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_mul_stochasticIntegralBrownian_indIoc
-- name    : LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:55:56.668659+00:00
-- url     : https://prove2.me/theorems/91977d7b-8b20-4979-a00e-655e616ee7ab
-- title:
--   mul stochasticIntegralBrownian indIoc
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc` is extracted from `LevyStochCalc.Brownian.ItoPullOut`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside an Itô integral over a window

A bounded `ℱ_a`-measurable weight times the Itô integral of an integrand supported in `(a, b]` is
the Itô integral of the weighted integrand: the weight times the indicator is itself a simple
integrand, so this is associativity against a simple integrand.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section PullOut

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (him : Measurable (Function.uncurry fun ω s => indIoc Ω a b ω s * K ω s))
    (hip : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s * K ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hvm : Measurable (Function.uncurry fun ω s => V ω * indIoc Ω a b ω s * K ω s))
    (hvp : Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s * K ω s)
    (hvq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖V ω * indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    (fun ω => V ω * stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => indIoc Ω a b ω s * K ω s) him hip hiq t ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => V ω * indIoc Ω a b ω s * K ω s) hvm hvp hvq t := by sorry
