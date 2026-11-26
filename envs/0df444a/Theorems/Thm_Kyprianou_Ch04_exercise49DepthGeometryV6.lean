-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49DepthGeometryV6
-- name    : Kyprianou.Ch04.exercise49DepthGeometryV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:33:26.840105+00:00
-- url     : https://prove2.me/theorems/703e65ff-e8a1-40ca-b27d-fea942660dae
-- title:
--   exercise49DepthGeometryV6
-- statement:
--   exercise49DepthGeometryV6
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49DepthGeometryV6
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hB : BddAbove (Set.range (fun t => -Y t))) (a : NNReal)
    (ha : (a : WithTop NNReal) = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ Y t < 0}) :
    (⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))).toReal =
      -Y a + (⨆ q : ℚ, ENNReal.ofReal (-(Y (a + Real.toNNReal q) - Y a))).toReal := by
  sorry
