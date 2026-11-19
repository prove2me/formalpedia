-- Prove2me | Theorems.Thm_Kyprianou_Ch01_weakDescendingStoppedConvolution
-- name    : Kyprianou.Ch01.weakDescendingStoppedConvolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:07:50.960403+00:00
-- url     : https://prove2.me/theorems/ad6ca582-896a-411a-8c76-174ed81e3cc7
-- title:
--   One-step killed-walk law is convolution of positive-prefix occupation with increment law
-- statement:
--   Condition on the first n increments of an independent identically distributed random walk. The last increment is independent of the first n and has law mu. On the strictly positive-prefix event, the probability that S(n+1) falls in a measurable B is the integral of mu(B - y) against the pushforward of the prefix-restricted law of S(n). The identity holds for every measurable B, without a nonpositive-set restriction.
-- source:
--   Kyprianou (2006), Exercise 1.8(ii), worked solution printed page 304

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.weakDescendingStoppedConvolution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (hindep : iIndepFun increment P)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hLaw : ∀ n : ℕ, HasLaw (increment n) mu P)
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    P {ω | S (n + 1) ω ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω} =
      ∫⁻ y : ℝ, mu ((fun z : ℝ => y + z) ⁻¹' B) ∂
        (Measure.map (S n)
          (P.restrict {ω | ∀ j : ℕ,
              1 ≤ j → j ≤ n → 0 < S j ω})) := by
  sorry
