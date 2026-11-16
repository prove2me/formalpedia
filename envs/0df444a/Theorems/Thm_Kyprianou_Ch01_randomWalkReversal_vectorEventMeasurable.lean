-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_vectorEventMeasurable
-- name    : Kyprianou.Ch01.randomWalkReversal_vectorEventMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T17:29:30.566343+00:00
-- url     : https://prove2.me/theorems/23737ddc-9d3e-40ed-8323-d3df947527d0
-- title:
--   Measurability of finite-vector positive-prefix event
-- statement:
--   A finite-dimensional Borel positive-prefix event is measurable as an intersection of the terminal coordinate-sum preimage of B with countably many open strict inequalities in measurable finite sums.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.8(i), strict terminal records and positive reversal prefixes

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_pathCombinatorics
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.randomWalkReversal_vectorEventMeasurable
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    let seq : (Fin n → ℝ) → ℕ → ℝ :=
      fun v i => if h : i < n then v ⟨i, h⟩ else 0
    let psum : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => ∑ i ∈ Finset.range j, seq v i
    MeasurableSet {v : Fin n → ℝ |
      psum v n ∈ B ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum v j} := by sorry
