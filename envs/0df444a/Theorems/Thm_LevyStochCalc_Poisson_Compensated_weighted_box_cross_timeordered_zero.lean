-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_weighted_box_cross_timeordered_zero
-- name    : LevyStochCalc.Poisson.Compensated.weighted_box_cross_timeordered_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T23:41:18.356739+00:00
-- url     : https://prove2.me/theorems/ad4fae52-73bb-4529-860c-68f1f246d525
-- title:
--   weighted box cross timeordered zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.weighted_box_cross_timeordered_zero` is extracted from `LevyStochCalc.Poisson.CompensatedDensityBoxIsometry`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted covariances of compensated boxes

Second moments and cross moments of compensated masses `Ñ((a,b] × A)` weighted by a
past-measurable factor: the weighted second moment, vanishing of the cross terms for disjoint
marks and for time-ordered boxes, and the same-time bilinear covariance in the marks. These
combine into the isometry for a single time interval carrying several marks.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.weighted_box_cross_timeordered_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b c d : ℝ} (hc : 0 ≤ c) (hbc : b ≤ c) (hcd : c < d)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A') (hA'f : ν A' ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ c) g) :
    ∫ ω, g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc c d ×ˢ A') ω) ∂P = 0 := by sorry
