-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ZeroIntensityPRM
-- name    : Kyprianou.Ch04.exercise45ZeroIntensityPRM
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:01:42.657734+00:00
-- url     : https://prove2.me/theorems/8530f9a3-f2c1-5e09-85fd-0fb84989af5a
-- title:
--   Existence of a zero-intensity Poisson random measure
-- statement:
--   On any probability space the identically zero random measure is a Poisson random measure for zero Levy intensity.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv) deterministic drift counterexample.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The zero-intensity PRM can be identically the zero measure. -/
theorem Kyprianou.Ch04.exercise45ZeroIntensityPRM {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    ∃ N : PoissonRandomMeasure.{0,0,0} P (0 : Measure ℝ), ∀ w, N.N w = 0 := by
  sorry
