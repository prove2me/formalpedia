-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOccupationFixedTimeAEMeasurableFromCadlag
-- name    : Kyprianou.Ch01.branchingOccupationFixedTimeAEMeasurableFromCadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:59:38.361465+00:00
-- url     : https://prove2.me/theorems/d380728b-a4b2-44aa-9db0-e1cd82b8294f
-- title:
--   Fixed-time Lamperti branching occupation clock is almost-everywhere measurable from càdlàg paths
-- statement:
--   For a natural-valued branching population process whose deterministic-time sections are measurable and whose sample paths are almost surely càdlàg, the source-faithful Lamperti occupation integral branchingOccupation Y t ω is P-almost-everywhere measurable at each fixed nonnegative time t. Construct a jointly measurable real-valued process Z agreeing with Y at all times on one conull set, using the now Proved branchingCadlagJointMeasurableRealVersion. Its integral over [0,t] is measurable by measurableRealOccupationIntervalIntegralOfJoint. On the same common full-measure event, equality of integrands holds for every real integration time, so the integrals agree. Transfer measurability using AEMeasurable.congr. No finite mean or total population moment assumptions.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4, exact branchingOccupation definition in Definitions.Def_Kyprianou_Ch01_BranchingClocks. Uses Proved Kyprianou.Ch01.branchingCadlagJointMeasurableRealVersion UUID 3e5ffb1c-118e-4f86-a96a-376c4f6afad2 and published Kyprianou.Ch01.measurableRealOccupationIntervalIntegralOfJoint UUID 033ceefa-7861-4ee6-8bfe-a209fc2e38b2. This prepares measurability of the inverse occupation clock and original Open branching path a50b477a-4a36-47b8-a220-857f6c082b64.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOccupationFixedTimeAEMeasurableFromCadlag
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℝ≥0 → Ω → ℕ)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∀ t : ℝ≥0,
      AEMeasurable (fun ω : Ω => branchingOccupation Y t ω) P := by
  sorry
