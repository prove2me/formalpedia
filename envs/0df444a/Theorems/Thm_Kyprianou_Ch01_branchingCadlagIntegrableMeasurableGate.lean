-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingCadlagIntegrableMeasurableGate
-- name    : Kyprianou.Ch01.branchingCadlagIntegrableMeasurableGate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:49:07.051733+00:00
-- url     : https://prove2.me/theorems/40bae473-1444-44e6-a4a2-4d9f1310c6c7
-- title:
--   Single measurable conull gate giving all-path càdlàg and interval-integrable branching population version
-- statement:
--   Construct a globally fixed-time measurable NNReal-indexed natural-valued population version W by choosing one measurable conull set G where both the original IsCadlag condition and interval integrability on every finite real interval hold. Use ae_iff, exists_measurable_superset_of_null, hCadlag and hInt to select G; set W(t,ω)=Y(t,ω) on G and 0 off G. Every W time section is globally measurable, and every sample path W is càdlàg and interval-integrable: on G by assumptions, outside G constant zero. On the same conull event G, W equals original Y simultaneously at every time. This is an exact source-faithful common-event repair, not strengthening the original almost-sure assumptions.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4. Connected direct child of Open branchingInverseOccupationMeasurablePathFromIntegrability UUID 4480b9d8-dd0a-45c8-98fd-b740a29378d6, itself linked through accepted sketches into root UUID 318afc19-2086-4e20-9846-225169aaa3c1. Existing Proved measurableConullCadlagGate 6fb7affb-823f-4e61-9d62-a64d07c25936 and pinned Mathlib measurable supersets of null sets.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingCadlagIntegrableMeasurableGate
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => Y t ω))
    (hInt : ∀ᵐ ω ∂P, ∀ a b : ℝ,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ)) volume a b) :
    ∃ W : ℝ≥0 → Ω → ℕ,
      (∀ t : ℝ≥0, Measurable (W t)) ∧
      (∀ ω : Ω, IsCadlag (fun t : ℝ≥0 => W t ω)) ∧
      (∀ (ω : Ω) (a b : ℝ),
        IntervalIntegrable
          (fun s : ℝ => (W (Real.toNNReal s) ω : ℝ)) volume a b) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, W t ω = Y t ω) := by
  sorry
