-- Prove2me | Theorems.Thm_OddGoldbach21_odd_sum_le_21_primes
-- name    : OddGoldbach21.odd_sum_le_21_primes
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T09:54:06.908148+00:00
-- url     : https://prove2.me/theorems/7c518abe-0516-466f-bd05-bade32a648a0
-- title:
--   Every odd number greater than one is a sum of at most 21 primes
-- statement:
--   Every odd natural number greater than one can be represented as a multiset of at most 21 primes whose sum is that number. Repetition is allowed. This is the unchanged Odd Goldbach campaign template with bound 21.
-- source:
--   Private refinement of https://prove2.me/theorems/82fdb6cc-2eda-4f2c-a3d7-72dacecba417 using the existing Rosser-Schoenfeld theta lower bound https://prove2.me/theorems/d4cf496a-eed1-4284-8d5d-f9cfbfb07786 . New constants derived locally, not claimed as quoted from the source.

import Mathlib

theorem OddGoldbach21.odd_sum_le_21_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 21 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by sorry
