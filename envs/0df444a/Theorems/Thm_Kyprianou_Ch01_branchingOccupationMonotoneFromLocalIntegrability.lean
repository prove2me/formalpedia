-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOccupationMonotoneFromLocalIntegrability
-- name    : Kyprianou.Ch01.branchingOccupationMonotoneFromLocalIntegrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:46:27.619631+00:00
-- url     : https://prove2.me/theorems/d8f15fb3-2392-499f-9abe-3ca8687b84d1
-- title:
--   Nonnegative population occupancy produces a nondecreasing Lamperti forward clock
-- statement:
--   For each population sample path Y:nonnegative time to natural-valued population, assume its real-valued path is locally interval integrable from time zero. Then the Lamperti occupation clock J(t)=integral from 0 to t of Y(s) is nondecreasing in t because Y(s) is nonnegative. This is a source-exact deterministic prerequisite to the forward Lamperti inverse recovery (1.17).
-- source:
--   Kyprianou (2006), Chapter 1 equation (1.17), occupation time change

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOccupationMonotoneFromLocalIntegrability
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hlocalint : ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume 0 (t : ℝ)) :
    Monotone (fun t : ℝ≥0 => branchingOccupation Y t ω) := by
  sorry
