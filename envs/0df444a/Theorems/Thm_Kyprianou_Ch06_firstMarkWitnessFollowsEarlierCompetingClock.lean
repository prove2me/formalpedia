-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkWitnessFollowsEarlierCompetingClock
-- name    : Kyprianou.Ch06.firstMarkWitnessFollowsEarlierCompetingClock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:10:26.003659+00:00
-- url     : https://prove2.me/theorems/b483dbed-6b71-416a-a4d2-a35a6a0be907
-- title:
--   Lemma 6.18: witnessed first mark follows the strictly earlier competing arrival clock
-- statement:
--   Suppose a finite arrival clock for marks in B precedes the first arrival into competing region D. If a witnessed first mark belongs to B∪D and has positive singleton count at that earlier clock, then the first mark lies in B. This bridges the first-mark witness assumption to the clock-race event used in the proper-overlap mark law.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, competing marked-Poisson first-arrival and first-mark region classification.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstMarkedWinnerRegionFromCompetingSurvival
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkWitnessFollowsEarlierCompetingClock
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (B D : Set E)
    (firstMark : Option E)
    (tauB : WithTop NNReal)
    (hFinite : tauB ≠ ⊤)
    (hEarlier : tauB <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D}))
    (hInitD : N omega 0 D = 0)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega (tauB.untopD 0) (S ∪ T) =
        N omega (tauB.untopD 0) S +
          N omega (tauB.untopD 0) T)
    (hWitness : ∃ x : E, firstMark = some x ∧ x ∈ B ∪ D ∧
      0 < N omega (tauB.untopD 0) ({x} : Set E)) :
    firstMark ∈ (some '' B) := by sorry
