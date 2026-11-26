-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41CappedClockStopV13
-- name    : Kyprianou.Ch04.exercise41CappedClockStopV13
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:56:42.522044+00:00
-- url     : https://prove2.me/theorems/1a9a718a-44e3-4e94-ba92-c00bd083a101
-- title:
--   Finite cap of a stopping time has measurable sublevel sets
-- statement:
--   Finite cap of a stopping time has measurable sublevel sets
-- source:
--   Kyprianou (2006), Exercise 4.1(ii) auxiliary result

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41CappedClockStopV13
    {Ω : Type} [MeasurableSpace Ω] (F : Filtration NNReal inferInstance)
    (raw : Ω → WithTop NNReal) (hr : IsStoppingTime F raw) (N : NNReal) :
    ∀ s : NNReal, MeasurableSet[F s] {w | (min (raw w) (N : WithTop NNReal)).untopD 0 ≤ s} := by
  sorry
