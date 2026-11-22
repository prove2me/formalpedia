-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingInverseOccupationAllPathMeasurable
-- name    : Kyprianou.Ch01.branchingInverseOccupationAllPathMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:49:00.750797+00:00
-- url     : https://prove2.me/theorems/0fe96d98-781e-419d-aea6-72598d71d138
-- title:
--   Global measurability of inverse occupation time for all-path càdlàg integrable population processes
-- statement:
--   If the natural-valued branching population W is measurable at every deterministic time, and all sample paths are càdlàg and globally interval-integrable on each finite real interval, then each inverse occupation time ω↦inverseBranchingOccupation W t ω is globally measurable into WithTop NNReal. Cast to Real; use public Proved rightContinuous_measurable_sections_joint_evaluation to obtain joint population measurability, public Proved measurableRealOccupationIntervalIntegralOfJoint for measurable occupation sections, and public Proved branchingOccupationContinuousFromGlobalIntervalIntegrability to obtain continuous occupation sample paths. The identity inverseBranchingOccupationEqFirstUpperPassage is Proved; apply the public Proved firstUpperPassageMeasurableOfContinuousPublic to conclude the source inverse clock is globally measurable for each t. This supplies the actual inversion theorem for §1.3.4, avoiding a new rational-clock formalisation.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4. Direct dependency of branchingInverseOccupationMeasurablePathFromIntegrability UUID 4480b9d8-dd0a-45c8-98fd-b740a29378d6, connected via SKETCH_ACCEPTED to §1.3.4 root. Public Proved firstUpperPassageMeasurableOfContinuousPublic 6d06f7df-f059-4757-98d3-608fbaec7bfc, source identity 2b44cec0-9be2-4673-87f0-36c88ad85a3c, occupation continuity 15f351ae-d8d6-4230-94f9-3995abb4e7d9, joint evaluation 8aafec11-d8a5-443c-9386-270a0d5c8a04 and interval integral measurable 033ceefa-7861-4ee6-8bfe-a209fc2e38b2.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingInverseOccupationAllPathMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (W : ℝ≥0 → Ω → ℕ)
    (hMeas : ∀ t : ℝ≥0, Measurable (W t))
    (hCadlag : ∀ ω : Ω, IsCadlag (fun t : ℝ≥0 => W t ω))
    (hInt : ∀ (ω : Ω) (a b : ℝ),
      IntervalIntegrable
        (fun s : ℝ => (W (Real.toNNReal s) ω : ℝ)) volume a b) :
    ∀ t : ℝ≥0,
      Measurable (fun ω : Ω => inverseBranchingOccupation W t ω) := by
  sorry
