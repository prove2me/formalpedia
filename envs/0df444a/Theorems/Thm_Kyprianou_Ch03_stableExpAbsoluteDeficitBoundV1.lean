-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableExpAbsoluteDeficitBoundV1
-- name    : Kyprianou.Ch03.stableExpAbsoluteDeficitBoundV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T18:19:12.254051+00:00
-- url     : https://prove2.me/theorems/a53e063b-bdf0-4746-a295-48556b75901c
-- title:
--   A uniform exponential deficit bound from a nonzero random variable
-- statement:
--   Convexity of the exponential implies an upper bound on the Laplace transform of a scaled absolute value, with a strictly positive deficit for a random variable that is not almost surely zero.
-- source:
--   Auxiliary lemma for Kyprianou (2006), Exercise 3.7, high-index stable process path variation.

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

theorem Kyprianou.Ch03.stableExpAbsoluteDeficitBoundV1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) (hne : ¬ Y =ᵐ[P] 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (∫ w, Real.exp (-s * |Y w|) ∂P) ≤ Real.exp (-c * s) := by sorry
