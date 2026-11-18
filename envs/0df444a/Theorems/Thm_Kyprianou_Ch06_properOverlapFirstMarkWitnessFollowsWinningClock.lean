-- Prove2me | Theorems.Thm_Kyprianou_Ch06_properOverlapFirstMarkWitnessFollowsWinningClock
-- name    : Kyprianou.Ch06.properOverlapFirstMarkWitnessFollowsWinningClock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:14:32.867198+00:00
-- url     : https://prove2.me/theorems/a678259b-3223-427a-ba2f-5cac99f746b5
-- title:
--   Lemma 6.18: a proper-overlap first-mark witness belongs to C when the A∩C clock wins
-- statement:
--   If the first arrival into A is the minimum of the two clocks into A∩C and A\C, and the first clock is finite and strictly earlier, then any witnessed first mark x in A with positive singleton count at the first A-arrival must lie in A∩C. This is the deterministic winner-event inclusion needed for the positive-intensity proper-overlap first-mark probability law.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, first-mark selection in the genuine two-positive-intensity competing Poisson regions.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstMarkWitnessFollowsEarlierCompetingClock
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.properOverlapFirstMarkWitnessFollowsWinningClock
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (A C : Set E)
    (firstMark : Option E) (tauB : WithTop NNReal)
    (hFinite : tauB ≠ ⊤)
    (hBefore : tauB < sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u (A \ C)}))
    (hTau : sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A}) =
      min tauB (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u (A \ C)})))
    (hInitD : N omega 0 (A \ C) = 0)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega (tauB.untopD 0) (S ∪ T) =
        N omega (tauB.untopD 0) S +
          N omega (tauB.untopD 0) T)
    (hWitness : ∃ x : E,
      firstMark = some x ∧ x ∈ A ∧
      0 < N omega ((sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})).untopD 0) ({x} : Set E)) :
    firstMark ∈ (some '' (A ∩ C)) := by sorry
