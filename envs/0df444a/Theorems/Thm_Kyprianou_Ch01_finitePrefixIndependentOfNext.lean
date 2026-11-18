-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finitePrefixIndependentOfNext
-- name    : Kyprianou.Ch01.finitePrefixIndependentOfNext
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:20:55.862076+00:00
-- url     : https://prove2.me/theorems/a8c8a460-bf2c-47c3-8019-fb7d99938c92
-- title:
--   The finite vector of past random-walk increments is independent of the next increment
-- statement:
--   For a family of measurable independent random increments, the finite-dimensional vector of increments at indices strictly less than n is independent of the increment at index n. This extracts the finite-history independence needed to factor the positive-prefix stopped law in Exercise 1.8(ii).
-- source:
--   Kyprianou (2006), Exercise 1.8(ii) first descending potential convolution, p.304

import Mathlib.Probability.Independence.Basic
open MeasureTheory ProbabilityTheory Set Finset
set_option autoImplicit false

theorem Kyprianou.Ch01.finitePrefixIndependentOfNext
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (hindep : iIndepFun increment P) (n : ℕ) :
    IndepFun (fun ω (i : Finset.range n) => increment i.1 ω)
      (increment n) P := by sorry
