-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableConullIntegerRightContinuousGate
-- name    : Kyprianou.Ch01.measurableConullIntegerRightContinuousGate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:49:41.353556+00:00
-- url     : https://prove2.me/theorems/27431bea-3491-463b-9a16-2149c994f8b7
-- title:
--   Measurable full-measure event for right-continuous integer-valued sample paths
-- statement:
--   Given a raw NNReal-indexed integer-valued process F with all-time right-continuous paths almost surely, select a globally measurable conull set G on which all right-continuity statements hold pointwise. Use the proved pattern Kyprianou.Ch01.measurableConullCadlagGate (natural-valued version): define bad set of paths with failure at some time, its P measure is zero by ae_iff; obtain a measurable null superset using exists_measurable_superset_of_null; take its complement. This handles the uncountable-time conjunction on one common conull event without assuming the raw good set measurable.
-- source:
--   Kyprianou Chapter 1 §1.3.4 reverse Lamperti. Direct child of published Kyprianou.Ch01.reverseLampertiNonexplosiveJointIntegerProcessVersion UUID 16c022df-d006-4521-8a26-2c3b085468b6, itself connected by a parent sketch to root ac1b29c6-5525-4344-a03d-7469824736ed. Reuses Proved measurableConullCadlagGate UUID 6fb7affb-823f-4e61-9d62-a64d07c25936 proof source.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableConullIntegerRightContinuousGate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ≥0 → Ω → ℤ)
    (hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t) :
    ∃ G : Set Ω, MeasurableSet G ∧
      (∀ᵐ ω ∂P, ω ∈ G) ∧
      ∀ ω ∈ G, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t := by
  sorry
