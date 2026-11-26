-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49StoppedPathProductV7
-- name    : Kyprianou.Ch04.exercise49StoppedPathProductV7
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T16:40:12.578599+00:00
-- url     : https://prove2.me/theorems/3f5018cd-0a1d-51dc-bac6-d9618b5936ad
-- title:
--   exercise49StoppedPathProductV7
-- statement:
--   exercise49StoppedPathProductV7
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49StoppedPathProductV7
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ)
    (a : Ω → NNReal) (ha : ∀ w, τ w ≠ ⊤ → τ w = (a w : WithTop NNReal))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t)
    (hmA : Measurable a) (hProg : IsStronglyProgressive F X)
    (hDet : ∀ (s : NNReal) (B : Set Ω), MeasurableSet[F s] B →
      Measure.map (fun w u => X (s+u) w-X s w) (P.restrict B) =
        P B • Measure.map (fun w u => X u w) P) :
    let D : Set Ω := {w | τ w ≠ ⊤}
    let I : Ω → ℝ := fun w => -X (a w) w
    let Z : Ω → NNReal → ℝ := fun w u => X (a w+u) w-X (a w) w
    Measure.map (fun w => (I w,Z w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map (fun w u => X u w) P) := by
  sorry
