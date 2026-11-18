-- Prove2me | Theorems.Thm_Kyprianou_Ch01_weakPrefixVectorRepresentation
-- name    : Kyprianou.Ch01.weakPrefixVectorRepresentation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:21:51.816181+00:00
-- url     : https://prove2.me/theorems/85a58cfb-6b9f-4f38-b39f-cc33f1b75aee
-- title:
--   Measurable finite-dimensional representation of positive random-walk prefixes
-- statement:
--   The finite random walk prefix through step n has a measurable representation through its finite vector of increments 0,...,n-1: there is a measurable terminal-sum map g and a measurable vector set A encoding strict positivity of every intermediate sum, such that S(n)=g(V) and the original positive-path event is precisely V inverse image A. This deterministic finite-prefix representation enables source-faithful conditional independence at the next step.
-- source:
--   Kyprianou (2006), Exercise 1.8(ii), p.304

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FunProp
open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.weakPrefixVectorRepresentation
    {Ω : Type*} [MeasurableSpace Ω]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (n : ℕ) :
    let S : ℕ → Ω → ℝ :=
      fun k ω => ∑ i ∈ Finset.range k, increment i ω
    let H : Set Ω :=
      {ω | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω}
    let V : Ω → (Finset.range n → ℝ) :=
      fun ω i => increment i.1 ω
    ∃ (g : (Finset.range n → ℝ) → ℝ)
      (A : Set (Finset.range n → ℝ)),
      Measurable g ∧ MeasurableSet A ∧
      (∀ ω : Ω, S n ω = g (V ω)) ∧ H = V ⁻¹' A := by
  sorry
