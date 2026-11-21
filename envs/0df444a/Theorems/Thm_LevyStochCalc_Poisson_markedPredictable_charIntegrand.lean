-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_markedPredictable_charIntegrand
-- name    : LevyStochCalc.Poisson.markedPredictable_charIntegrand
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:25:17.149771+00:00
-- url     : https://prove2.me/theorems/63a9a5b9-776f-46ef-9ace-c7354cb42979
-- title:
--   markedPredictable charIntegrand
-- statement:
--   The source theorem `LevyStochCalc.Poisson.markedPredictable_charIntegrand` is extracted from `LevyStochCalc.Poisson.CharacterIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F000

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

theorem _root_.LevyStochCalc.Poisson.markedPredictable_charIntegrand {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Probability.MarkedPredictable ℱ ν (charIntegrand N w Bfam A T) := by sorry
