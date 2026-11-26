-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RecoveryGateV1
-- name    : Kyprianou.Ch04.exercise46RecoveryGateV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:24:09.738635+00:00
-- url     : https://prove2.me/theorems/c85d6fa8-65fa-5e5a-8b06-251e17d0e9a8
-- title:
--   Measurability of the first-arrival recovery test at a deterministic time
-- statement:
--   At deterministic time r, cap the first arrival clock at r. Its capped value and the current surplus are measurable at r. On A<r the capped value agrees with the first arrival time, so the strict recovery test is measurable.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RecoveryGateV1
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (r : NNReal) :
    MeasurableSet[G.rightCont r]
      {w | A w < (r : WithTop NNReal) ∧ (((A w).untopD 0 : NNReal) : Real) < L.X r w} := by
  sorry
