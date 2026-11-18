-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkStrictInfDiv
-- name    : Kyprianou.Ch01.geometricStoppedWalkStrictInfDiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:55:01.782461+00:00
-- url     : https://prove2.me/theorems/36cf2e9d-e190-4ff7-9f18-8128ebcb4f45
-- title:
--   Infinite divisibility of IID random sums with independent strict geometric count
-- statement:
--   For 0<p<1, the law of the finite random sum of IID real increments stopped at an independent geometric count of parameter p is infinitely divisible. This strict-parameter result is the nontrivial random-sum content of Kyprianou (2006), Chapter 1, Exercise 1.2(ii), preserving all source independence and measurability hypotheses.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), strict geometric count.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricStoppedWalkStrictInfDiv
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ,
      HasLaw (increment n) jumpLaw P)
    (hGeometric : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal (p * (1 - p) ^ k))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    LevyFoundations.isInfinitelyDivisibleLaw
      (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) := by
  sorry
