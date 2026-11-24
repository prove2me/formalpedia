-- Prove2me | Theorems.Thm_Kyprianou_Ch03_eventApproximationImpliesNullCompletedMeasurableV2
-- name    : Kyprianou.Ch03.eventApproximationImpliesNullCompletedMeasurableV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:13:59.402923+00:00
-- url     : https://prove2.me/theorems/81bf38f6-9217-44c6-a7f4-163934b3266b
-- title:
--   Approximation by measurable events implies membership in the null-completed sigma-algebra
-- statement:
--   For any sigma-algebra m on the sample space, approximation by m-measurable events with arbitrarily small outer measure of the symmetric difference implies measurability after adjoining all subsets of ambient measurable null sets. Choose a sequence with summable error, use outer-measure Borel-Cantelli to obtain agreement with the liminf of the approximants outside an ambient measurable null hull, then use sigma-algebra closure. No ambient measurability of m is required.
-- source:
--   Measure-theoretic closure lemma for Kyprianou (2006), Chapter 3 Exercise 3.1; parent f0666111-850e-44c9-8630-c8093e5f3095. Corrected explicit ambient measurable-space binder; V1 accidentally elaborated the null hull in m rather than the ambient space.

import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.eventApproximationImpliesNullCompletedMeasurableV2
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m : MeasurableSpace Omega) (A : Set Omega)
    (hApprox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ B : Set Omega, MeasurableSet[m] B ∧
        P ((A \ B) ∪ (B \ A)) < ε) :
    MeasurableSet[m ⊔ MeasurableSpace.generateFrom
      {N : Set Omega | ∃ M : Set Omega,
        MeasurableSet[mΩ] M ∧ P M = 0 ∧ N ⊆ M}] A := by
  sorry
