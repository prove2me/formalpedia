-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45PRMNoOriginVersionV2
-- name    : Kyprianou.Ch04.exercise45PRMNoOriginVersionV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:21:54.313832+00:00
-- url     : https://prove2.me/theorems/fad7996c-6b7b-4fc2-93e8-afc007e1ae9d
-- title:
--   PRM version without initial atoms (Chapter 4 compatible imports)
-- statement:
--   Choose an indistinguishable PRM with no time-zero mass on any path.
-- source:
--   Kyprianou Exercise 4.5; compatible Chapter 4 PRM definition imports.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Choose an indistinguishable PRM with no atom at time zero on any path. -/
theorem Kyprianou.Ch04.exercise45PRMNoOriginVersionV2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (h0 : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0) :
    ∃ N' : PoissonRandomMeasure.{0,0,0} P ν,
      (∀ᵐ w ∂P, N'.N w = N.N w) ∧
      (∀ w, N'.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0) := by
  sorry
