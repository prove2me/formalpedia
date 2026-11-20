-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_compensated_cross_covariance
-- name    : LevyStochCalc.Poisson.Compensated.compensated_cross_covariance
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:52:27.018762+00:00
-- url     : https://prove2.me/theorems/4321ee4a-43f3-4160-8c2c-1cfd3da10a59
-- title:
--   compensated cross covariance
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.compensated_cross_covariance` is extracted from `LevyStochCalc.Poisson.CompensatedDensityStepIntegral`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Step (finite-sum) predictable integrands

The compensated integral of a finite family of simple predictable integrands, its martingale
property and square-integrability on the natural filtration, together with the covariance
identities for compensated masses of disjoint and of nested space-time sets that underlie the
`L²` isometry.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Step (finite-sum) predictable integrands

The mark-discretised approximant is rank-`>1` in the mark, so it is a finite
`ℝ`-combination of `SimplePredictable` pieces rather than a single one. Its
compensated integral is the sum of the pieces' integrals, and (being a sum of the
per-piece martingales) it is again a martingale on the natural filtration. -/

theorem _root_.LevyStochCalc.Poisson.Compensated.compensated_cross_covariance
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hfin' : LevyStochCalc.Poisson.referenceIntensity ν B' ≠ ⊤) :
    ∫ ω, N.compensated B ω * N.compensated B' ω ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal := by sorry
