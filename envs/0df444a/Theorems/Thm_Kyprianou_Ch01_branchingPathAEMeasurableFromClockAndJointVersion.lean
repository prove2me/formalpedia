-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingPathAEMeasurableFromClockAndJointVersion
-- name    : Kyprianou.Ch01.branchingPathAEMeasurableFromClockAndJointVersion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:26:21.766275+00:00
-- url     : https://prove2.me/theorems/717d518d-5df9-498d-b61b-cd37a82af031
-- title:
--   Complete Lamperti branching path measurability from a measurable inverse clock and jointly measurable population version
-- statement:
--   Assume a jointly measurable real-valued population version Z agrees with natural Y at every observation time on one common P-conull event. Assume a sectionwise globally measurable inverse occupation clock version C agrees with source inverseBranchingOccupation simultaneously at all levels on another common conull event. Then the original entire Lamperti forward path ω↦(t↦(branchingToPoisson Y t ω:ℤ)) is almost everywhere measurable into the uncountable-index product path space. For each level t, measurably evaluate the jointly measurable Z at the finite clock C t, using a measurable WithTop-to-NNReal default at top, and choose 0 for top. Take Int.floor to recover integer-valued states. Assemble every time coordinate by measurable_pi_iff. On intersection of the two common conull events, this globally measurable representative equals the original path at every t, including the infinite-clock extinction convention. Avoid trying to use aemeasurable_pi_iff over uncountable indices.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4. Direct child of canonical Open a50b477a-4a36-47b8-a220-857f6c082b64 through a new accepted sketch. Reuses public Proved branchingCadlagJointMeasurableRealVersion UUID 3e5ffb1c-118e-4f86-a96a-376c4f6afad2 and new companion branchingInverseOccupationMeasurablePathVersion.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingPathAEMeasurableFromClockAndJointVersion
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (C : ℝ≥0 → Ω → WithTop ℝ≥0)
    (hCMeas : ∀ t : ℝ≥0, Measurable (C t))
    (hCEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      C t ω = inverseBranchingOccupation Y t ω)
    (Z : ℝ≥0 → Ω → ℝ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2))
    (hSame : ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      Z s ω = (Y s ω : ℝ)) :
    AEMeasurable
      (fun ω : Ω => fun t : ℝ≥0 =>
        (branchingToPoisson Y t ω : ℤ)) P := by
  sorry
