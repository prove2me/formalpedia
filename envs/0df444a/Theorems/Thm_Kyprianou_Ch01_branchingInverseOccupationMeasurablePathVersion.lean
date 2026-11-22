-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingInverseOccupationMeasurablePathVersion
-- name    : Kyprianou.Ch01.branchingInverseOccupationMeasurablePathVersion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:26:19.283361+00:00
-- url     : https://prove2.me/theorems/986baeef-6b97-457a-9783-ef97e53a3f8b
-- title:
--   A measurable complete inverse occupation-clock path version for a càdlàg branching population
-- statement:
--   Under fixed-time measurable NNReal-indexed natural population and P-a.e. càdlàg paths, construct for each level t a globally measurable WithTop NNReal random inverse-occupation time C t. The construction must agree with the exact source inverseBranchingOccupation Y t simultaneously for every level t on one common conull set. Use a globally jointly measurable population version, deterministic local integrability and continuity of the occupation primitive on all càdlàg paths, and the publicly proved strict firstUpperPassage measurable rational clock. Critical: uniform agreement across uncountably many levels is required for the target path-space AEMeasurable statement; separate pointwise a.e. results are insufficient. The source-level inverseBranchingOccupationEqFirstUpperPassage identity gives passage-time equivalence without finite offspring moments.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4, exact inverseBranchingOccupation and branchingOccupation. Direct child of canonical Open branchingToPoissonPathAEMeasurableFromCadlag a50b477a-4a36-47b8-a220-857f6c082b64, root 318afc19-2086-4e20-9846-225169aaa3c1. Existing Proved branchingCadlagJointMeasurableRealVersion 3e5ffb1c-118e-4f86-a96a-376c4f6afad2, branchingOccupationFixedTimeAEMeasurableFromCadlag d380728b-a4b2-44aa-9db0-e1cd82b8294f, branchingOccupationContinuousFromGlobalIntervalIntegrability 15f351ae-d8d6-4230-94f9-3995abb4e7d9, and firstUpperPassageMeasurableOfContinuousPublic 6d06f7df-f059-4757-98d3-608fbaec7bfc. New identity inverseBranchingOccupationEqFirstUpperPassage UUID 2b44cec0-9be2-4673-87f0-36c88ad85a3c.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingInverseOccupationMeasurablePathVersion
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∃ C : ℝ≥0 → Ω → WithTop ℝ≥0,
      (∀ t : ℝ≥0, Measurable (C t)) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        C t ω = inverseBranchingOccupation Y t ω := by
  sorry
