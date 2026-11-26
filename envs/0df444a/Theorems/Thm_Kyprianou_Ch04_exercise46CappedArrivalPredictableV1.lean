-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46CappedArrivalPredictableV1
-- name    : Kyprianou.Ch04.exercise46CappedArrivalPredictableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:14:27.343181+00:00
-- url     : https://prove2.me/theorems/fe69d95b-1ad1-5290-b44a-26a1d4870385
-- title:
--   Capped arrival time is a predictable continuous process
-- statement:
--   The stopped clock at deterministic time t is measurable in the filtration at t. Each capped-clock path is a minimum of a constant and the identity, or the identity for an infinite arrival time. Apply the predictable continuous adapted process theorem.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46CappedArrivalPredictableV1
    {Omega : Type} [m : MeasurableSpace Omega]
    (G : Filtration NNReal m)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A) :
    IsStronglyPredictable G.rightCont
      (fun t w => (((min (A w) (t : WithTop NNReal)).untopD 0 : NNReal) : Real)) := by
  sorry
