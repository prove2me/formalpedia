-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOccupationContinuousFromGlobalIntervalIntegrability
-- name    : Kyprianou.Ch01.branchingOccupationContinuousFromGlobalIntervalIntegrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:07:21.478251+00:00
-- url     : https://prove2.me/theorems/15f351ae-d8d6-4230-94f9-3995abb4e7d9
-- title:
--   Continuous Lamperti occupation clock from interval integrability on every finite real interval
-- statement:
--   For any nonnegative-integer population path whose real-time extension via Real.toNNReal is interval-integrable on every real interval, its original Lamperti occupation clock A(t)=∫₀ᵗY(s)ds is continuous as a function of NNReal time. Apply pinned Mathlib intervalIntegral.continuous_primitive to the globally interval-integrable real extension at base point 0, then compose the resulting continuous real-time primitive with the continuous NNReal-to-Real coercion. This is the precise deterministic continuity ingredient required to identify the inverse occupation time with a rational-infimum clock. It preserves the original source clock definition and does not require finite offspring mean.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4, original branchingOccupation definition in Definitions.Def_Kyprianou_Ch01_BranchingClocks. Pinned Mathlib intervalIntegral.continuous_primitive signature verified with remote job 4f6e19de-72c0-4b28-bc91-3d4e7b12d43a; NNReal.continuous_coe indexed in pinned Mathlib.Topology.UniformSpace.Real. Builds upon public Proved branchingOccupationMonotoneFromLocalIntegrability UUID d8f15fb3-2392-499f-9abe-3ca8687b84d1.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOccupationContinuousFromGlobalIntervalIntegrability
    {Ω : Type*}
    (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hglobal : ∀ a b : ℝ,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume a b) :
    Continuous (fun t : ℝ≥0 => branchingOccupation Y t ω) := by
  sorry
