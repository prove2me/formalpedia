-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_forwardEventEncoding
-- name    : Kyprianou.Ch01.randomWalkReversal_forwardEventEncoding
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T17:29:39.380262+00:00
-- url     : https://prove2.me/theorems/39fb205b-e754-4a4f-af8a-49f9545aeb32
-- title:
--   Original positive-prefix event as measurable finite-vector event
-- statement:
--   For prefixes no longer than n, converting the first n scalar increments into a Fin n vector preserves every prefix sum and therefore the positive-prefix event.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.8(i), strict terminal records and positive reversal prefixes

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_pathCombinatorics
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.randomWalkReversal_forwardEventEncoding
    {Ω : Type*} (increment : ℕ → Ω → ℝ)
    (n : ℕ) (B : Set ℝ) :
    let seq : (Fin n → ℝ) → ℕ → ℝ :=
      fun v i => if h : i < n then v ⟨i, h⟩ else 0
    let psum : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => ∑ i ∈ Finset.range j, seq v i
    ∀ ω : Ω,
      ((∑ i ∈ Finset.range n, increment i ω) ∈ B ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ n →
          0 < ∑ i ∈ Finset.range j, increment i ω) ↔
      (    psum (fun i : Fin n => increment i ω) n ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n →
        0 < psum (fun i : Fin n => increment i ω) j) := by sorry
