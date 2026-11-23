-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_runningSup_path_structure_of_cadlag
-- name    : Kyprianou.Ch08.StageB.runningSup_path_structure_of_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:08:25.590033+00:00
-- url     : https://prove2.me/theorems/c4d424d4-b357-4c20-b0b8-e20ca612e75a
-- title:
--   Running supremum of a càdlàg path: monotonicity, domination, and compact-index representation
-- statement:
--   For one càdlàg sample path starting at zero, the running supremum is monotone, dominates the path, and equals the indexed supremum over the closed interval. These are the exact structural inputs required by the proved running-supremum continuity theorems.
-- source:
--   Derived from the exact target preamble and the source-faithful regularity block of candidates 46582, 46591, 46624, and 46635. The compact interval representation is the set equality in the pinned runningSup definition.

import Mathlib.Topology.Order.LeftRight
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.runningSup_path_structure_of_cadlag
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : IsCadlag fun t => X t ω) (hX0 : X 0 ω = 0) :
    Monotone (fun t : ℝ≥0 => runningSup X t ω) ∧
    (∀ t : ℝ≥0, X t ω ≤ runningSup X t ω) ∧
    (∀ T : ℝ≥0, runningSup X T ω = ⨆ u : Icc (0 : ℝ≥0) T, X u.1 ω) := by sorry
