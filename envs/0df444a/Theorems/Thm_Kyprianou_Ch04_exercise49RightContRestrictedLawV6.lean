-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RightContRestrictedLawV6
-- name    : Kyprianou.Ch04.exercise49RightContRestrictedLawV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:35:42.866797+00:00
-- url     : https://prove2.me/theorems/1ba74337-595f-4a52-8eee-085bba63d5c9
-- title:
--   exercise49RightContRestrictedLawV6
-- statement:
--   exercise49RightContRestrictedLawV6
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RightContRestrictedLawV6
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hDet : ∀ (s : NNReal) (B : Set Ω), MeasurableSet[F s] B →
      Measure.map (fun w u => X (s+u) w-X s w) (P.restrict B) =
        P B • Measure.map (fun w u => X u w) P)
    (s : NNReal) (B : Set Ω) (hB : MeasurableSet[F.rightCont s] B) :
    Measure.map (fun w u => X (s+u) w-X s w) (P.restrict B) =
      P B • Measure.map (fun w u => X u w) P := by
  sorry
