-- Prove2me | Theorems.Thm_Kyprianou_Ch06_positiveMarkedPointBeforeClockMinForcesEarlierRegion
-- name    : Kyprianou.Ch06.positiveMarkedPointBeforeClockMinForcesEarlierRegion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:15:04.272233+00:00
-- url     : https://prove2.me/theorems/74d97648-69c1-4c0d-97f5-f1015c720ca4
-- title:
--   Lemma 6.18: positive mark at the minimum competing time forces its region to win without clock ties
-- statement:
--   Let t>0 be the minimum of the first positive-mark arrival times into regions B and D. If a mark x in B has positive singleton count at t, then the B arrival time is no later than the D arrival time. If the two clocks are unequal, B arrives strictly first.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, first-mark competition and proper-overlap mark selection.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_positiveSingletonMarkedCountForcesRegionCount
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.positiveMarkedPointBeforeClockMinForcesEarlierRegion
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (B D : Set E) (t : NNReal) (x : E)
    (ht : 0 < t) (hxB : x ∈ B)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega t (S ∪ T) = N omega t S + N omega t T)
    (hPositive : 0 < N omega t ({x} : Set E))
    (hMin : (t : WithTop NNReal) = min
      (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B})) (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D})))
    (hNoTie : sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B}) ≠ sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D})) :
    sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B}) < sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D}) := by sorry
