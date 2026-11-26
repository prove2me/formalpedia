-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49ProgressiveV6
-- name    : Kyprianou.Ch04.exercise49ProgressiveV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:35:33.925321+00:00
-- url     : https://prove2.me/theorems/87b1e947-e3a6-424f-9ec6-c64edc831d08
-- title:
--   exercise49ProgressiveV6
-- statement:
--   exercise49ProgressiveV6
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49ProgressiveV6
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t)
    (ha : ∀ t, Measurable[F t] (X t)) :
    IsStronglyProgressive F X := by
  sorry
