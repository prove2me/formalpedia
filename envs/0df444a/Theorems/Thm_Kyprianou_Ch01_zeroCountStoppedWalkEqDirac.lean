-- Prove2me | Theorems.Thm_Kyprianou_Ch01_zeroCountStoppedWalkEqDirac
-- name    : Kyprianou.Ch01.zeroCountStoppedWalkEqDirac
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:51:28.289214+00:00
-- url     : https://prove2.me/theorems/a86b7f27-a407-4a29-9bf6-41a25d553dda
-- title:
--   Stopped random walk with almost-sure zero count has Dirac-zero law
-- statement:
--   For a probability space and random count N that is almost surely zero, any random sum of the first N increments has point-mass law at zero. This supplies the p=1 endpoint of the source-faithful geometric stopped-random-walk infinite-divisibility theorem, independently of the increment distribution.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2: boundary case p=1 for a geometrically stopped random walk.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.zeroCountStoppedWalkEqDirac
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hNzero : P {ω | N ω = 0} = 1) :
    P.map (fun ω =>
      ∑ i ∈ Finset.range (N ω), increment i ω) =
      Measure.dirac (0 : ℝ) := by
  sorry
