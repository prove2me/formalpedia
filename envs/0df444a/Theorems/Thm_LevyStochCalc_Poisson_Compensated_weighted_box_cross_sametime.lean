-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_weighted_box_cross_sametime
-- name    : LevyStochCalc.Poisson.Compensated.weighted_box_cross_sametime
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:36:01.700166+00:00
-- url     : https://prove2.me/theorems/dbc44803-2ae9-4cb1-b5cd-b558d93fc83c
-- title:
--   weighted box cross sametime
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.weighted_box_cross_sametime` is extracted from `LevyStochCalc.Poisson.CompensatedDensityBoxIsometry`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000

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

theorem _root_.LevyStochCalc.Poisson.Compensated.weighted_box_cross_sametime
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hAf : ν A ≠ ⊤) (hA'f : ν A' ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P
      = (∫ ω, g ω ∂P)
        * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal := by sorry
