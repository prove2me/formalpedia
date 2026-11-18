-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomCountIndependentSumCharFunMixture
-- name    : Kyprianou.Ch01.randomCountIndependentSumCharFunMixture
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:32:21.242432+00:00
-- url     : https://prove2.me/theorems/9478e9b1-6943-4167-885e-bd33372b0029
-- title:
--   Characteristic function of an independent random count stopped sum as its discrete mixture
-- statement:
--   For a measurable ℕ-valued stopping count independent of the entire measurable real mark sequence, the characteristic function of the stopped finite sum equals the countable sum of count probabilities times the characteristic functions of the corresponding fixed-length sums. No IID assumption is required for this conditional-factorisation identity. This is the exact missing conditioning step for Kyprianou Chapter 1 Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), conditioning on the independent geometric count, backed by pinned Mathlib product-law and countable-integral theorems.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.randomCountIndependentSumCharFunMixture
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P)
    (xi : ℝ) :
    charFun (P.map (fun ω =>
      ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
      ∑' n : ℕ,
        ((P {ω | N ω = n}).toReal : ℂ) *
        charFun (P.map (fun ω =>
          ∑ i ∈ Finset.range n, increment i ω)) xi := by
  sorry
