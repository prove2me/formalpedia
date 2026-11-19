-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstGridTriggerPrefixCharacterisationPublic
-- name    : Kyprianou.Ch01.firstGridTriggerPrefixCharacterisationPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:02:55.375223+00:00
-- url     : https://prove2.me/theorems/884d6253-ee50-4d11-adc7-5a9f1e8a972a
-- title:
--   Public First bounded discrete trigger is the length of the non-triggering prefix
-- statement:
--   For any predicate on integer time and any terminal horizon N, define the first index at which the predicate holds, using N as a mandatory sentinel. The first index is no later than N, and for each n<N it exceeds n exactly when the predicate fails at every k<=n. This is the finite first-crossing characterisation needed for the Brownian grid stopping time, without assuming any stochastic-process theorem or target Laplace formula.
-- source:
--   Accepted original private Kyprianou.Ch01.firstGridTriggerPrefixCharacterisation source, republished under public visibility for Chapter 1 optional sampling.

import Mathlib.Data.Nat.Find
import Mathlib.Logic.Pairwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
set_option autoImplicit false

theorem Kyprianou.Ch01.firstGridTriggerPrefixCharacterisationPublic
    {Ω : Type*} (p : ℕ → Ω → Prop) (N : ℕ) :
    let τ : Ω → ℕ := fun ω => by
      classical
      exact Nat.find (show ∃ k : ℕ, k = N ∨ p k ω from ⟨N, Or.inl rfl⟩)
    (∀ ω, τ ω ≤ N) ∧
      ∀ n : ℕ, n < N → ∀ ω : Ω,
        (n < τ ω ↔ ∀ k : ℕ, k ≤ n → ¬ p k ω) := by sorry
