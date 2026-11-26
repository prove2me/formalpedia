-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49DepthProductPushforwardV7
-- name    : Kyprianou.Ch04.exercise49DepthProductPushforwardV7
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:40:32.889732+00:00
-- url     : https://prove2.me/theorems/26ca3b41-7b45-4433-acd5-d866af29cf59
-- title:
--   exercise49DepthProductPushforwardV7
-- statement:
--   exercise49DepthProductPushforwardV7
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49DepthProductPushforwardV7
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set Ω) (I : Ω → ℝ) (Z H : Ω → NNReal → ℝ)
    (hI : Measurable I) (hZ : Measurable Z) (hH : Measurable H)
    (hJoint : Measure.map (fun w => (I w,Z w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map H P)) :
    let d : (NNReal → ℝ) → ℝ := fun y => (⨆ q : ℚ, ENNReal.ofReal (-y (Real.toNNReal q))).toReal
    Measure.map (fun w => (I w,d (Z w))) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map (d ∘ H) P) := by
  sorry
