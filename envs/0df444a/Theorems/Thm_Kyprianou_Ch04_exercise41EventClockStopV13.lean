-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41EventClockStopV13
-- name    : Kyprianou.Ch04.exercise41EventClockStopV13
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:56:39.692114+00:00
-- url     : https://prove2.me/theorems/2f142721-6b0e-4aad-8d4c-43935d96e619
-- title:
--   Single deterministic event clock is a stopping time
-- statement:
--   Single deterministic event clock is a stopping time
-- source:
--   Kyprianou (2006), Exercise 4.1(ii) auxiliary result

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41EventClockStopV13
    {Ω : Type} [MeasurableSpace Ω] (F : Filtration NNReal inferInstance)
    (t : NNReal) (A : Set Ω) (hA : MeasurableSet[F t] A) :
    IsStoppingTime F (fun w => if w ∈ A then (t : WithTop NNReal) else ⊤) := by
  sorry
