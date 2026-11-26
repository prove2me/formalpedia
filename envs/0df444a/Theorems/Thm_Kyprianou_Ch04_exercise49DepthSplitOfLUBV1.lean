-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49DepthSplitOfLUBV1
-- name    : Kyprianou.Ch04.exercise49DepthSplitOfLUBV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:45:38.971091+00:00
-- url     : https://prove2.me/theorems/7ba40cc6-063d-4f35-bd24-e4a9b858e9eb
-- title:
--   The all-time depth splits into the first deficit and the shifted future depth
-- statement:
--   The all-time depth splits into the first deficit and the shifted future depth
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49DepthSplitOfLUBV1
    (Y : NNReal → ℝ) (t : NNReal) (d e : ℝ)
    (hpre : ∀ u : NNReal, u < t → 0 ≤ Y u)
    (ht : Y t ≤ 0)
    (hd : IsLUB (Set.range (fun u => -Y u)) d)
    (he : IsLUB (Set.range (fun u => -(Y (t + u) - Y t))) e) :
    d = -Y t + e := by
  sorry
