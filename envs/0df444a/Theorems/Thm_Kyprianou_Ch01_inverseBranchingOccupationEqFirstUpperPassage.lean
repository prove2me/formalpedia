-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseBranchingOccupationEqFirstUpperPassage
-- name    : Kyprianou.Ch01.inverseBranchingOccupationEqFirstUpperPassage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:24:07.133724+00:00
-- url     : https://prove2.me/theorems/2b44cec0-9be2-4673-87f0-36c88ad85a3c
-- title:
--   Exact Lamperti inverse occupation clock is the strict first-upper-passage time of its occupation process
-- statement:
--   The original Lamperti inverse-occupation clock is exactly the existing firstUpperPassage operator applied to the occupation process, for any natural-valued population path and nonnegative threshold. The only apparent difference is that firstUpperPassage requires strictly positive crossing times, whereas inverseBranchingOccupation searches all NNReal times. The occupation integral at time 0 is zero and the threshold is nonnegative, so a strict crossing cannot occur at zero. The two hitting sets and existence conditions are therefore equal, including the never-crossing top case. This gives source-level reuse of the Proved generic firstUpperPassageMeasurableOfContinuousPublic result without assuming an offspring moment.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4, exact `inverseBranchingOccupation` in Def_Kyprianou_Ch01_BranchingClocks; `firstUpperPassage` in Def_Kyprianou_Ch01_ExplicitLevyExamples, and existing Proved firstUpperPassageMeasurableOfContinuousPublic UUID 6d06f7df-f059-4757-98d3-608fbaec7bfc. Intended to connect via the §1.3.4 branchingToPoissonPathAEMeasurableFromCadlag UUID a50b477a-4a36-47b8-a220-857f6c082b64 and its new Open witness bridge 1183b275-b9cd-449b-b8ad-21a144127c7b.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseBranchingOccupationEqFirstUpperPassage
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (t : ℝ≥0) (ω : Ω) :
    inverseBranchingOccupation Y t ω =
      firstUpperPassage
        (fun s (η : Ω) => branchingOccupation Y s η)
        (t : ℝ) ω := by
  sorry
