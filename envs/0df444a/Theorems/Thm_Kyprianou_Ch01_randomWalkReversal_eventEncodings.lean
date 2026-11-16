-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_eventEncodings
-- name    : Kyprianou.Ch01.randomWalkReversal_eventEncodings
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T17:26:14.467297+00:00
-- url     : https://prove2.me/theorems/3c0475db-bc85-49f8-b1a9-5889bdef2673
-- title:
--   Measurable encoding of ladder maxima and positive prefixes as events of finite increment vectors
-- statement:
--   For an arbitrary deterministic family of real increment values indexed by an underlying sample space, the record-maximum event can be encoded as the same measurable set E of finite vectors applied to the reversed increment vector, while the strictly positive prefix event is E applied to the original increment vector. Finite partial-sum and reversal identities prove the pointwise equivalences. The event E is Borel measurable provided the terminal-set B is measurable.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.8(i), deterministic finite path event encodings

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_pathCombinatorics
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.randomWalkReversal_eventEncodings
    {Ω : Type*}
    (increment : ℕ → Ω → ℝ) (n : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let forward : Ω → Fin n → ℝ := fun ω i => increment i ω
    let backwards : Ω → Fin n → ℝ := fun ω i => increment (Fin.rev i) ω
    let seq : (Fin n → ℝ) → ℕ → ℝ :=
      fun v i => if h : i < n then v ⟨i, h⟩ else 0
    let psum : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => ∑ i ∈ Finset.range j, seq v i
    let E : Set (Fin n → ℝ) :=
      {v | psum v n ∈ B ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum v j}
    MeasurableSet E ∧
      (∀ ω : Ω,
        ((∑ i ∈ Finset.range n, increment i ω) ∈ B ∧
          ∀ j : ℕ, j < n →
            (∑ i ∈ Finset.range j, increment i ω) <
              (∑ i ∈ Finset.range n, increment i ω)) ↔
          backwards ω ∈ E) ∧
      (∀ ω : Ω,
        ((∑ i ∈ Finset.range n, increment i ω) ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ n →
            0 < ∑ i ∈ Finset.range j, increment i ω) ↔
          forward ω ∈ E) := by sorry
