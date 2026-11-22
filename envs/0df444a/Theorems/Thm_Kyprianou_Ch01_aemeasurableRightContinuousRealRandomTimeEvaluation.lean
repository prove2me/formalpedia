-- Prove2me | Theorems.Thm_Kyprianou_Ch01_aemeasurableRightContinuousRealRandomTimeEvaluation
-- name    : Kyprianou.Ch01.aemeasurableRightContinuousRealRandomTimeEvaluation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:40:47.183077+00:00
-- url     : https://prove2.me/theorems/74ed6524-e545-40dc-bdb3-0bd5fb653135
-- title:
--   Almost-everywhere measurable evaluation of a right-continuous process at a measurable random time
-- statement:
--   Let F be a real-valued process with globally measurable fixed-time sections and sample paths that are simultaneously right-continuous at all NNReal times on a common P-conull event. For any globally measurable finite NNReal random time T, the random-time evaluation ω↦F(T ω,ω) is P-almost-everywhere measurable. Construct measurable countable-time approximants F(c_n(T ω),ω), where c_n is the dyadic ceiling of T. Every approximant is measurable by measurable_from_prod_countable_right and measurable Nat.ceil. The dyadic ceilings approach T from the right, so the all-time right-continuity condition gives almost-sure convergence. Invoke Mathlib's aemeasurable_of_tendsto_metrizable_ae. This supplies the exact stochastic random-time evaluation step required when applying the Lamperti inverse occupation clock, and does not assume all sample paths are right-continuous.
-- source:
--   Kyprianou 2006 Chapter 1 §1.3.4 forward Lamperti inverse occupation time change; generalised directly from actual accepted proof source of AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation UUID 8aafec11-d8a5-443c-9386-270a0d5c8a04 to the a.e. setting using verified pinned Mathlib aemeasurable_of_tendsto_metrizable_ae. Supports public Open Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromCadlag UUID a50b477a-4a36-47b8-a220-857f6c082b64.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.aemeasurableRightContinuousRealRandomTimeEvaluation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (F t))
    (hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t)
    (T : Ω → ℝ≥0) (hT : Measurable T) :
    AEMeasurable (fun ω : Ω => F (T ω) ω) P := by
  sorry
