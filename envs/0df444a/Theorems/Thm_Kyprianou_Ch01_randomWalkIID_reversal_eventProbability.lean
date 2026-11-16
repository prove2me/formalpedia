-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomWalkIID_reversal_eventProbability
-- name    : Kyprianou.Ch01.randomWalkIID_reversal_eventProbability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T17:20:43.212676+00:00
-- url     : https://prove2.me/theorems/d25ea8c5-0f52-474d-a095-5be58e78f1aa
-- title:
--   Any measurable event in an i.i.d. increment vector is invariant in probability under reversal
-- statement:
--   Equality in distribution of a finite i.i.d. increment vector and its reversal implies the same probability for every measurable set of finite vectors. This is the event-level transport needed to convert the deterministic record/ladder reversal identity into an equality of random-walk event probabilities.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.8(i); finite iid joint law reversal event consequence

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkIID_reversal_jointLaw
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.randomWalkIID_reversal_eventProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ i : ℕ, Measurable (increment i))
    (hindep : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hLaw : ∀ i : ℕ, HasLaw (increment i) jumpLaw P)
    (n : ℕ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    P {ω | (fun i : Fin n => increment i ω) ∈ E} =
      P {ω | (fun i : Fin n => increment (Fin.rev i) ω) ∈ E} := by sorry
