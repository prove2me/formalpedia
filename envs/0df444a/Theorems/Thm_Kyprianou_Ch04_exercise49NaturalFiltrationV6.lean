-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49NaturalFiltrationV6
-- name    : Kyprianou.Ch04.exercise49NaturalFiltrationV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:37:30.66243+00:00
-- url     : https://prove2.me/theorems/acdc1751-5800-45c2-a4d2-ff39f261b0f1
-- title:
--   exercise49NaturalFiltrationV6
-- statement:
--   exercise49NaturalFiltrationV6
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49NaturalFiltrationV6
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t) :
    ∃ F : Filtration NNReal (inferInstance : MeasurableSpace Ω),
      (∀ t, Measurable[F t] (X t)) ∧
      ∀ (s : NNReal) (B : Set Ω), MeasurableSet[F s] B →
        Measure.map (fun w u => X (s+u) w-X s w) (P.restrict B) =
          P B • Measure.map (fun w u => X u w) P := by
  sorry
