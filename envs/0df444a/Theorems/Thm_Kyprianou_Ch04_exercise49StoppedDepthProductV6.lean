-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49StoppedDepthProductV6
-- name    : Kyprianou.Ch04.exercise49StoppedDepthProductV6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T16:37:21.562924+00:00
-- url     : https://prove2.me/theorems/b9320698-13f7-50bd-b810-f821917c5ab1
-- title:
--   exercise49StoppedDepthProductV6
-- statement:
--   exercise49StoppedDepthProductV6
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49StoppedDepthProductV6
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t)
    (a : Ω → NNReal) (ha : Measurable a)
    (hExact : ∀ w, (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t w < 0}) ≠ ⊤ →
      (sInf {v : WithTop NNReal | ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0}) =
        (a w : WithTop NNReal)) :
    let τ : Ω → WithTop NNReal := fun w => sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0}
    let D : Set Ω := {w | τ w ≠ ⊤}
    let I : Ω → ℝ := fun w => -X (a w) w
    let V : Ω → ℝ := fun w => (⨆ q : ℚ, ENNReal.ofReal (-X (Real.toNNReal q) w)).toReal
    let W : Ω → ℝ := fun w => (⨆ q : ℚ, ENNReal.ofReal (-(X (a w + Real.toNNReal q) w - X (a w) w))).toReal
    Measure.map (fun w => (I w,W w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map V P) := by
  sorry
