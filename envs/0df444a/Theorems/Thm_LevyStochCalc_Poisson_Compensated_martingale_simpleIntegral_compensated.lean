-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_martingale_simpleIntegral_compensated
-- name    : LevyStochCalc.Poisson.Compensated.martingale_simpleIntegral_compensated
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:46:59.00268+00:00
-- url     : https://prove2.me/theorems/e09f79b2-c504-4a57-9e4d-b8f67bf9b6c8
-- title:
--   martingale simpleIntegral compensated
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.martingale_simpleIntegral_compensated` is extracted from `LevyStochCalc.Poisson.CompensatedMartingaleAdapted`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingale property of the simple compensated-Poisson integral

`simpleIntegral N φ` is adapted to a Poisson filtration `ℱ` of `N`: each time-rectangle
`timeRect i t` lies in the past `Iic t ×ˢ univ`, so its compensated mass is `ℱ_t`-measurable,
and the coefficient `ξᵢ` is `ℱ_t`-measurable once `t` reaches the partition point (the term
vanishing before). Each summand is `P`-integrable, its conditional expectation satisfies
`𝔼[ξᵢ·Ñ(timeRect i t) | ℱ_s] =ᵐ ξᵢ·Ñ(timeRect i s)` for `0 ≤ s ≤ t`, and summing over the
partition gives the martingale property of `t ↦ simpleIntegral N φ t`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.martingale_simpleIntegral_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => simpleIntegral N φ t)
      ℱ P := by sorry
