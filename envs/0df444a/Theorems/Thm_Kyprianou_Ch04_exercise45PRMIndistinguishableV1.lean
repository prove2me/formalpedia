-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45PRMIndistinguishableV1
-- name    : Kyprianou.Ch04.exercise45PRMIndistinguishableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:15:07.63356+00:00
-- url     : https://prove2.me/theorems/0e56386e-3480-409d-8cf3-422dda33f5d7
-- title:
--   Poisson random measure law under indistinguishable measurable modifications
-- statement:
--   Measurable modifications equal almost surely as measures preserve all Poisson random measure fields, including countable-family and joint past-future independence.
-- source:
--   Kyprianou Exercise 4.5, version normalisation

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A measurable almost-sure modification of a Poisson random measure preserves its law. -/
theorem Kyprianou.Ch04.exercise45PRMIndistinguishableV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (Q : Ω → Measure (ℝ × ℝ))
    (hQ : ∀ B : Set (ℝ × ℝ), MeasurableSet B → Measurable (fun w => Q w B))
    (hEq : ∀ᵐ w ∂P, N.N w = Q w) :
    ∃ N' : PoissonRandomMeasure.{0,0,0} P ν, N'.N = Q := by
  sorry
