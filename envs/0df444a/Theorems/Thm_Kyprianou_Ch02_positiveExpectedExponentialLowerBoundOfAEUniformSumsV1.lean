-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveExpectedExponentialLowerBoundOfAEUniformSumsV1
-- name    : Kyprianou.Ch02.positiveExpectedExponentialLowerBoundOfAEUniformSumsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:47:28.231473+00:00
-- url     : https://prove2.me/theorems/592f786e-0b8c-48d3-b029-5bd570353dbf
-- title:
--   Uniformly bounded nonnegative random sums have uniformly positive expected negative exponentials
-- statement:
--   The countable extended supremum of nonnegative random sums is measurable and finite almost everywhere by the uniform bound. Its negative exponential, after taking toReal, is positive and bounded by one. Its expectation is positive and is a common lower bound for the negative exponential expectations of every sum.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, bounded-variation Lévy paths and Lévy-triplet characterisation.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveExpectedExponentialLowerBoundOfAEUniformSumsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : ℕ → Ω → ℝ)
    (hm : ∀ n, AEMeasurable (S n) P)
    (hn : ∀ n ω, 0 ≤ S n ω)
    (hb : ∀ᵐ ω ∂P, ∃ B : ℝ, ∀ n, S n ω ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c ≤ ∫ ω, Real.exp (-(S n ω)) ∂P := by
  sorry
