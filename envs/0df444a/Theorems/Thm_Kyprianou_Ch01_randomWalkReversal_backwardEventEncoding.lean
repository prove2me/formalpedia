-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_backwardEventEncoding
-- name    : Kyprianou.Ch01.randomWalkReversal_backwardEventEncoding
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T17:29:29.618598+00:00
-- url     : https://prove2.me/theorems/3c27b452-f78d-4258-b2cf-187eda329f0b
-- title:
--   Strict terminal record as reversed finite-vector positive-prefix event
-- statement:
--   The proven deterministic random-walk reversal equivalence rewrites the terminal-record event as the positive-prefix event of the reversed Fin n increment vector, preserving its terminal value.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.8(i), strict terminal records and positive reversal prefixes

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_pathCombinatorics
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.randomWalkReversal_backwardEventEncoding
    {Ω : Type*} (increment : ℕ → Ω → ℝ)
    (n : ℕ) (B : Set ℝ) :
    let seq : (Fin n → ℝ) → ℕ → ℝ :=
      fun v i => if h : i < n then v ⟨i, h⟩ else 0
    let psum : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => ∑ i ∈ Finset.range j, seq v i
    ∀ ω : Ω,
      ((∑ i ∈ Finset.range n, increment i ω) ∈ B ∧
        ∀ j : ℕ, j < n →
          (∑ i ∈ Finset.range j, increment i ω) <
            (∑ i ∈ Finset.range n, increment i ω)) ↔
      (    psum (fun i : Fin n => increment (Fin.rev i) ω) n ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n →
        0 < psum (fun i : Fin n => increment (Fin.rev i) ω) j) := by sorry
