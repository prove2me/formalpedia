-- Prove2me | Theorems.Thm_Kyprianou_Ch06_arrivalSurvivalLowerBound
-- name    : Kyprianou.Ch06.arrivalSurvivalLowerBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:57:54.765546+00:00
-- url     : https://prove2.me/theorems/6664f5f9-30c9-4338-8898-5ffc3b189109
-- title:
--   Chapter 6 Poisson first arrival: survival lower-bound via later zero count
-- statement:
--   For a count process monotone almost surely, the probability that the first positive A-count is strictly after t is bounded below by the probability of zero A-count at any later deterministic time s>t. This is the lower sandwich component for Lemma 6.18 survival.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.arrivalSurvivalLowerBound
    {Omega E : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (N : Omega → NNReal → Set E → Nat) (A : Set E)
    (hMono : ∀ᵐ omega ∂P, Monotone (fun t : NNReal => N omega t A))
    (s t : NNReal) (hts : t < s) :
    P {omega | N omega s A = 0} ≤
    P {omega | (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})} := by sorry
