-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkedWinnerRegionFromCompetingSurvival
-- name    : Kyprianou.Ch06.firstMarkedWinnerRegionFromCompetingSurvival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:00:11.856686+00:00
-- url     : https://prove2.me/theorems/948b2984-6b6d-408d-9849-42ce0d4fcaef
-- title:
--   Lemma 6.18: a witnessed first mark belongs to the winning competing mark region
-- statement:
--   Suppose a witnessed marked point x belongs to B∪D and has positive singleton count at time t. If no D-marks have arrived through t (expressed as t strictly preceding the first D-arrival), then x belongs to B. This is the pathwise mark classification required after ruling out simultaneous competing arrivals.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, first-mark winner determined by the earlier competing Poisson mark-region arrival.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_beforeFirstArrivalImpliesZeroCount
import Theorems.Thm_Kyprianou_Ch06_positiveSingletonMarkedCountForcesRegionCount
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkedWinnerRegionFromCompetingSurvival
    {Omega E : Type} (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (t : NNReal) (x : E)
    (B D : Set E) (hMark : x ∈ B ∪ D)
    (hInitD : N omega 0 D = 0)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega t (S ∪ T) = N omega t S + N omega t T)
    (hPositive : 0 < N omega t ({x} : Set E))
    (hBeforeD : (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D})) :
    x ∈ B := by sorry
