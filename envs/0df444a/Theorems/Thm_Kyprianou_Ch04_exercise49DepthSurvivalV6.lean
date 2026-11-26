-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49DepthSurvivalV6
-- name    : Kyprianou.Ch04.exercise49DepthSurvivalV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:33:13.650871+00:00
-- url     : https://prove2.me/theorems/f87f1017-0ef2-5c69-9e00-197e8a0988ac
-- title:
--   exercise49DepthSurvivalV6
-- statement:
--   exercise49DepthSurvivalV6
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49DepthSurvivalV6
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hB : BddAbove (Set.range (fun t => -Y t)))
    (x : ℝ) (hx : 0 ≤ x) :
    (⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))).toReal ≤ x ↔
      (sInf {v : WithTop NNReal | ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ x + Y t < 0}) = ⊤ := by
  sorry
