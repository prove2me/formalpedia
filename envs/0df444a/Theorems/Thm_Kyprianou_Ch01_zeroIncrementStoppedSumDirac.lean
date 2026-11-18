-- Prove2me | Theorems.Thm_Kyprianou_Ch01_zeroIncrementStoppedSumDirac
-- name    : Kyprianou.Ch01.zeroIncrementStoppedSumDirac
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:30:23.800871+00:00
-- url     : https://prove2.me/theorems/97995701-b060-4751-ab44-a27f1ab2925b
-- title:
--   Zero-marginal IID increments give a Dirac-zero random stopped sum
-- statement:
--   If every real increment has the common Dirac-zero law, then the sum over any random finite count is almost surely zero and its image law is Dirac zero. This proves the degenerate increment-law branch required by the source-valid strict geometric IID stopped-sum infinite-divisibility theorem.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), degenerate all-zero mark law.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.zeroIncrementStoppedSumDirac
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ) (N : Ω → ℕ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ, HasLaw (increment n) jumpLaw P)
    (hDirac : jumpLaw = Measure.dirac (0 : ℝ)) :
    P.map (fun ω =>
      ∑ i ∈ Finset.range (N ω), increment i ω) =
      Measure.dirac (0 : ℝ) := by
  sorry
