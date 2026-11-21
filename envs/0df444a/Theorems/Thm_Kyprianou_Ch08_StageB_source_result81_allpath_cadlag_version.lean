-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_allpath_cadlag_version
-- name    : Kyprianou.Ch08.StageB.source_result81_allpath_cadlag_version
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:40:09.520633+00:00
-- url     : https://prove2.me/theorems/3d233f99-4182-42a0-bed9-5cb0f5d7df64
-- title:
--   A measurable all-path version of a real càdlàg process
-- statement:
--   Almost-sure càdlàg paths with no positive jumps admit an indistinguishable process with everywhere càdlàg paths, everywhere no positive jumps, zero start and measurable coordinates. Choose measurable versions at a countable dense time set and use right continuity to recover every clock simultaneously.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Source-faithful decomposition of b5430c32-5738-4ad5-9956-e8891a1d6407.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_allpath_cadlag_version
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t, AEMeasurable (X t) P)
    (hzero : X 0 = fun _ => 0)
    (hcad : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))
    (hjump : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s => X s ω) (nhdsWithin t (Iio t)) (nhds l) → X t ω ≤ l) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t, Y t ω = X t ω) ∧
      (∀ t, Measurable (Y t)) ∧ (Y 0 = fun _ => 0) ∧
      (∀ ω, IsCadlag (fun t => Y t ω)) ∧
      (∀ (ω : Ω) (t : ℝ≥0) (l : ℝ), 0 < t →
        Tendsto (fun s => Y s ω) (nhdsWithin t (Iio t)) (nhds l) → Y t ω ≤ l) := by
  sorry
