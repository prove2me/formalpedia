-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomWalkReversalLadderIdentity
-- name    : Kyprianou.Ch01.randomWalkReversalLadderIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:22:02.626021+00:00
-- url     : https://prove2.me/theorems/23dfd350-fcbc-46b1-8351-9250ccb73ad1
-- title:
--   Exercise 1.8(i): random-walk ladder maxima and reversed positive paths
-- statement:
--   Kyprianou Exercise 1.8(i): for a real random walk with IID increments, the joint distribution of the nth sum being a new strict maximum above all preceding sums equals the joint distribution of the nth sum when all partial sums from 1 to n are strictly positive. This is the finite-dimensional time-reversal identity used to derive the Cramér–Lundberg integrated-tail result in Theorem 1.9. Draft pending remote Lean elaboration.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.8(i), printed p. 29.

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.randomWalkReversalLadderIdentity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ i : ℕ, Measurable (increment i))
    (hindep : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hLaw : ∀ i : ℕ, HasLaw (increment i) jumpLaw P) :
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    ∀ (n : ℕ), 1 ≤ n →
      ∀ B : Set ℝ, MeasurableSet B →
        P {ω | S n ω ∈ B ∧
          ∀ j : ℕ, j < n → S j ω < S n ω} =
        P {ω | S n ω ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω} := by
  sorry
