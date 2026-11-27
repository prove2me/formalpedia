-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45PRMNoOriginVersionV1
-- name    : Kyprianou.Ch04.exercise45PRMNoOriginVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:19:27.204565+00:00
-- url     : https://prove2.me/theorems/730385e0-a3bc-547c-a135-270bd8887892
-- title:
--   Indistinguishable Poisson random measure with no initial atom
-- statement:
--   Choose a Poisson random measure equal to the original almost surely and with zero time-zero mass on every sample.
-- source:
--   Kyprianou Exercise 4.5, original-space cutoff data

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Choose an indistinguishable PRM with no atom at time zero on any path. -/
theorem Kyprianou.Ch04.exercise45PRMNoOriginVersionV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (h0 : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0) :
    ∃ N' : PoissonRandomMeasure.{0,0,0} P ν,
      (∀ᵐ w ∂P, N'.N w = N.N w) ∧
      (∀ w, N'.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0) := by
  sorry
