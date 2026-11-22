-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingCadlagJointMeasurableRealVersion
-- name    : Kyprianou.Ch01.branchingCadlagJointMeasurableRealVersion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:54:11.125201+00:00
-- url     : https://prove2.me/theorems/3e5ffb1c-118e-4f86-a96a-376c4f6afad2
-- title:
--   Jointly measurable real-valued version of an almost-surely càdlàg natural population process
-- statement:
--   For any NNReal-indexed natural-valued stochastic process with measurable fixed-time sections and almost surely càdlàg paths, construct a real-valued process Z that is jointly measurable on NNReal×Ω and agrees with the original population cast to Real at every time on one common P-conull event. Choose a measurable conull càdlàg event G by the public measurableConullCadlagGate theorem. Define Z(t,ω)=Y(t,ω) on G and 0 elsewhere. All sample paths of Z are right-continuous: on G by càdlàg and continuity of the Nat-to-Real cast, off G because the path is constant. Each fixed-time section of Z is measurable by a measurable if-expression. Apply the public Proved AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation to conclude joint measurability. This is the exact source-faithful foundation for measurability of the Lamperti occupation integral.
-- source:
--   Kyprianou 2006 Ch01 §1.3.4 Lamperti forward branching occupation clock; uses accepted public AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation UUID 8aafec11-d8a5-443c-9386-270a0d5c8a04 and new public Kyprianou.Ch01.measurableConullCadlagGate, whose publication job is cb824d8e-98b7-441a-baec-b96320afb007. Supports Open Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromCadlag UUID a50b477a-4a36-47b8-a220-857f6c082b64.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingCadlagJointMeasurableRealVersion
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℝ≥0 → Ω → ℕ)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∃ Z : ℝ≥0 → Ω → ℝ,
      Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Z t ω = (Y t ω : ℝ)) := by
  sorry
