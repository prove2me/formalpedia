-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingInverseOccupationMeasurablePathFromIntegrability
-- name    : Kyprianou.Ch01.branchingInverseOccupationMeasurablePathFromIntegrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:35:20.330023+00:00
-- url     : https://prove2.me/theorems/4480b9d8-dd0a-45c8-98fd-b740a29378d6
-- title:
--   Measurable inverse Lamperti clock version under almost-sure càdlàg paths and interval integrability
-- statement:
--   Construct a measurable-section version C(t,ω) of the original inverse Lamperti occupation clock under a.e. càdlàg sample paths and a.e. integrability on every finite real interval. First select a measurable conull event on which both regularity conditions hold, gate the population Y to zero outside it, and deduce all-path regularity and interval integrability of the gated process. Each gated deterministic-time section is measurable, so the gated population is jointly measurable by the Proved rightContinuous_measurable_sections_joint_evaluation, and each occupation integral is measurable by the Proved measurableRealOccupationIntervalIntegralOfJoint. The gated occupation primitive is continuous for all sample paths by Proved branchingOccupationContinuousFromGlobalIntervalIntegrability. Identify its exact inverse with the strict firstUpperPassage of its occupation process using the newly Proved inverseBranchingOccupationEqFirstUpperPassage, then apply the Proved firstUpperPassageMeasurableOfContinuousPublic to establish that each gated inverse-clock section is globally measurable. On the common conull gate the process agrees with source Y at every time, so inverse clocks agree simultaneously at all levels. This makes the AEMeasurable path-space theorem possible without importing private proofs or asserting global regularity of the original raw process.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4. Imported public Proved firstUpperPassageMeasurableOfContinuousPublic 6d06f7df-f059-4757-98d3-608fbaec7bfc; inverseBranchingOccupationEqFirstUpperPassage 2b44cec0-9be2-4673-87f0-36c88ad85a3c; measurableConullCadlagGate 6fb7affb-823f-4e61-9d62-a64d07c25936; branchingOccupationContinuousFromGlobalIntervalIntegrability 15f351ae-d8d6-4230-94f9-3995abb4e7d9; measurableRealOccupationIntervalIntegralOfJoint 033ceefa-7861-4ee6-8bfe-a209fc2e38b2; rightContinuous_measurable_sections_joint_evaluation 8aafec11-d8a5-443c-9386-270a0d5c8a04. Intended to be connected through a new A-level accepted sketch to §1.3.4 root.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingInverseOccupationMeasurablePathFromIntegrability
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => Y t ω))
    (hInt : ∀ᵐ ω ∂P, ∀ a b : ℝ,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume a b) :
    ∃ C : ℝ≥0 → Ω → WithTop ℝ≥0,
      (∀ t : ℝ≥0, Measurable (C t)) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        C t ω = inverseBranchingOccupation Y t ω := by
  sorry
