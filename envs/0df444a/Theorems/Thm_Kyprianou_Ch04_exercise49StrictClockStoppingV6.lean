-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49StrictClockStoppingV6
-- name    : Kyprianou.Ch04.exercise49StrictClockStoppingV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:35:50.39782+00:00
-- url     : https://prove2.me/theorems/ec1c4771-d737-420b-9d8e-e6040eac813a
-- title:
--   exercise49StrictClockStoppingV6
-- statement:
--   exercise49StrictClockStoppingV6
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49StrictClockStoppingV6
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t)
    (h0 : ∀ w, X 0 w = 0)
    (ha : ∀ t, Measurable[F t] (X t)) :
    IsStoppingTime F.rightCont (fun w => sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0}) := by
  sorry
