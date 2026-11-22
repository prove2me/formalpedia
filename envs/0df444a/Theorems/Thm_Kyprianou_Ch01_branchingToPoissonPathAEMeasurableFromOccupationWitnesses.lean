-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingToPoissonPathAEMeasurableFromOccupationWitnesses
-- name    : Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromOccupationWitnesses
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T19:13:48.356873+00:00
-- url     : https://prove2.me/theorems/1183b275-b9cd-449b-b8ad-21a144127c7b
-- title:
--   Measurability of the branching inverse-clock path given measurable occupation and jointly measurable population witnesses
-- statement:
--   Establish a.e. measurability of the original forward Lamperti time-changed population path in the uncountable-index product space. Assume (i) all fixed-time branching occupation integrals are a.e. measurable, (ii) a jointly measurable real-valued population version agrees with the original at every time on a common conull event, and (iii) sampling Y at each measurable finite NNReal random time is a.e. measurable. Construct a measurable inverse occupation clock by applying rational upper-level tests on the population version and handle the top/infinite case, then establish measurable random-time evaluation and transfer to the complete path map on a single conull event. These hypotheses are discharged by already Proved separate lemmas from the Kyprianou Ch01 Lamperti programme. The hard remaining problem is the inverse-clock construction and simultaneous path measurability, which must genuinely be proved before the original milestone closes.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4; direct child of public Open Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromCadlag UUID a50b477a-4a36-47b8-a220-857f6c082b64, itself imported via SKETCH_ACCEPTED in Kyprianou.Ch01.lampertiForwardPathMapsAEMeasurableWithoutMoment UUID d346ccdb-3e68-4130-b078-6746f99dd872, itself imported from root 318afc19-2086-4e20-9846-225169aaa3c1. Uses proved branchOccupationFixedTimeAEMeasurableFromCadlag d380728b-a4b2-44aa-9db0-e1cd82b8294f; branchingCadlagJointMeasurableRealVersion 3e5ffb1c-118e-4f86-a96a-376c4f6afad2; aemeasurableCadlagNaturalRandomTimeEvaluation fa15311c-386d-41cf-b249-ed0816342762.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromOccupationWitnesses
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hOccupation : ∀ t : ℝ≥0,
      AEMeasurable (fun ω : Ω => branchingOccupation Y t ω) P)
    (Z : ℝ≥0 → Ω → ℝ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2))
    (hSame : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Z t ω = (Y t ω : ℝ))
    (hRandomEval : ∀ (T : Ω → ℝ≥0), Measurable T →
      AEMeasurable (fun ω : Ω => (Y (T ω) ω : ℝ)) P) :
    AEMeasurable
      (fun ω : Ω => fun t : ℝ≥0 =>
        (branchingToPoisson Y t ω : ℤ)) P := by
  sorry
