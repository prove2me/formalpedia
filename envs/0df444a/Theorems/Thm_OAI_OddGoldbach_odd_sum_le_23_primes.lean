-- Prove2me | Theorems.Thm_OAI_OddGoldbach_odd_sum_le_23_primes
-- name    : OAI.OddGoldbach.odd_sum_le_23_primes
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:44:31.316949+00:00
-- url     : https://prove2.me/theorems/82fdb6cc-2eda-4f2c-a3d7-72dacecba417
-- title:
--   Every odd number greater than 1 is the sum of at most 23 primes
-- statement:
--   Every odd natural number greater than 1 can be written as a sum of at most 23 primes. Repetition is allowed and order is irrelevant; the summands form a multiset. This is the Odd Goldbach campaign statement with bound 23.
-- source:
--   Numerical refinement of the accepted 25-prime Schnirelmann–Mann formalization https://prove2.me/theorems/ba75c64f-9452-4582-83b3-77b31da8e4dc . It uses a newly certified 1000-prime finite sieve set and the existing Riesel–Vaughan interval inputs; the shared definitions and quantified campaign goal are unchanged. This is a formalized constant improvement of the existing method, not a new proof of weak Goldbach.

import Mathlib

theorem OAI.OddGoldbach.odd_sum_le_23_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 23 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
