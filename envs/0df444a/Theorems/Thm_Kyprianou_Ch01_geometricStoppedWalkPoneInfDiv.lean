-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkPoneInfDiv
-- name    : Kyprianou.Ch01.geometricStoppedWalkPoneInfDiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:52:27.130885+00:00
-- url     : https://prove2.me/theorems/0ea4d520-86ef-4728-86d1-e8ea40c6044d
-- title:
--   Geometrically stopped random-walk law is infinitely divisible at p=1
-- statement:
--   For the p=1 geometric count distribution, N=0 almost surely and the stopped sum of independent increments (of any law) is identically zero; hence its law is Dirac zero and infinitely divisible. This is the p=1 boundary branch of Kyprianou Chapter 1's geometrically stopped random-walk exercise.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), geometric stopping boundary p=1.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
open MeasureTheory ProbabilityTheory LevyFoundations
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricStoppedWalkPoneInfDiv
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hGeometricOne : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal ((1 : ℝ) * (1 - (1 : ℝ)) ^ k)) :
    LevyFoundations.isInfinitelyDivisibleLaw
      (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) := by
  sorry
