-- Prove2me | Theorems.Thm_Kyprianou_Ch01_iidFixedLengthCharFun
-- name    : Kyprianou.Ch01.iidFixedLengthCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:26:38.561521+00:00
-- url     : https://prove2.me/theorems/cdf72878-961a-49d2-8426-33859d771d06
-- title:
--   Characteristic function of a fixed-length IID real random sum
-- statement:
--   For IID measurable real increments having the same probability law jumpLaw, the characteristic function of their first n-term sum equals the nth power of the common characteristic function. This exact fixed-count ingredient supports conditioning on the independent geometric stopping variable in Kyprianou (2006), Chapter 1, Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), finite IID sum prior to geometric stopping.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.iidFixedLengthCharFun
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ, HasLaw (increment n) jumpLaw P)
    (n : ℕ) (xi : ℝ) :
    charFun (P.map (fun ω =>
      ∑ i ∈ Finset.range n, increment i ω)) xi =
      (charFun jumpLaw xi) ^ n := by
  sorry
