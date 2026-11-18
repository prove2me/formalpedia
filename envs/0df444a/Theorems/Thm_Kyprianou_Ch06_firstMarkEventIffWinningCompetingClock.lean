-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkEventIffWinningCompetingClock
-- name    : Kyprianou.Ch06.firstMarkEventIffWinningCompetingClock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:23:07.345866+00:00
-- url     : https://prove2.me/theorems/62aa2cb6-29aa-4cd8-afe1-3bb1dea9daeb
-- title:
--   Lemma 6.18: witnessed first-mark event is equivalent to strictly winning competing arrival clock when no ties occur
-- statement:
--   Let t>0 be the minimum of the first arrival times into regions B and D. Assume the arrival clocks do not tie and a witnessed positive singleton mark at time t belongs to B∪D. Then the observed first mark lies in B exactly when the first B-arrival strictly precedes the first D-arrival. This provides the pathwise event equivalence connecting first-mark conditional laws with the exponential competing-clocks calculation.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, proper-overlap first-mark law and independent exponential race.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstMarkWitnessFollowsEarlierCompetingClock
import Theorems.Thm_Kyprianou_Ch06_positiveMarkedPointBeforeClockMinForcesEarlierRegion
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkEventIffWinningCompetingClock
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (B D : Set E) (firstMark : Option E)
    (t : NNReal) (ht : 0 < t)
    (hMin : (t : WithTop NNReal) =
      min
        (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u B}))
        (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u D})))
    (hNoTie :
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B}) ≠
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D}))
    (hInitD : N omega 0 D = 0)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega t (S ∪ T) = N omega t S + N omega t T)
    (hWitness : ∃ x : E, firstMark = some x ∧ x ∈ B ∪ D ∧
      0 < N omega t ({x} : Set E)) :
    (firstMark ∈ (some '' B) ↔
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B}) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D})) := by sorry
