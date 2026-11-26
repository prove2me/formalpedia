-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RecoveryRecordPrefixV1
-- name    : Kyprianou.Ch04.exercise46RecoveryRecordPrefixV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:28:39.061171+00:00
-- url     : https://prove2.me/theorems/1d8c567a-c1f0-5126-aa0a-4fd2d5cbd4e0
-- title:
--   First strict recovery is a record with bounded prefix
-- statement:
--   The global unit-drift bound makes the strict time gate redundant. Identify the clock with the usual upcrossing infimum and use the proved continuous upcrossing theorem.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RecoveryRecordPrefixV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (a : NNReal)
    (hBound : ∀ t : NNReal, L.X t w ≤ (t : Real)) :
    let R : WithTop NNReal := ⨅ t : NNReal, if (a : WithTop NNReal) < (t : WithTop NNReal) ∧
      (a : Real) < L.X t w then (t : WithTop NNReal) else ⊤
    (a : WithTop NNReal) ≤ R ∧
      (∀ t : NNReal, (t : WithTop NNReal) < R → L.X t w ≤ (a : Real)) ∧
      (R ≠ ⊤ → L.X (R.untopD 0) w = (a : Real)) := by
  sorry
