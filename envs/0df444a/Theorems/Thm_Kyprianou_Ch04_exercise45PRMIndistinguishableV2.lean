-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45PRMIndistinguishableV2
-- name    : Kyprianou.Ch04.exercise45PRMIndistinguishableV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:21:58.032649+00:00
-- url     : https://prove2.me/theorems/3aaecc37-5d2e-4ec2-8d98-6684970198f0
-- title:
--   PRM law under indistinguishable modifications (Chapter 4 compatible imports)
-- statement:
--   All Poisson random measure fields are preserved by measurable indistinguishable modifications.
-- source:
--   Kyprianou Exercise 4.5; compatible Chapter 4 PRM definition imports.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A measurable almost-sure modification of a Poisson random measure preserves its law. -/
theorem Kyprianou.Ch04.exercise45PRMIndistinguishableV2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (Q : Ω → Measure (ℝ × ℝ))
    (hQ : ∀ B : Set (ℝ × ℝ), MeasurableSet B → Measurable (fun w => Q w B))
    (hEq : ∀ᵐ w ∂P, N.N w = Q w) :
    ∃ N' : PoissonRandomMeasure.{0,0,0} P ν, N'.N = Q := by
  sorry
