-- Prove2me | Theorems.Thm_OAI_OddGoldbach_odd_sum_le_25_primes
-- name    : OAI.OddGoldbach.odd_sum_le_25_primes
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-24T11:02:44.199645+00:00
-- url     : https://prove2.me/theorems/ba75c64f-9452-4582-83b3-77b31da8e4dc
-- title:
--   Every odd number greater than 1 is the sum of at most 25 primes
-- statement:
--   Every odd natural number greater than 1 is a sum of at most 25 primes, with repetitions allowed. The proof refines the numerical estimates in xuanji's accepted 27-prime proof: the two-prime sum count is at least 100n/2399 for log n between 22 and 300 and for log n at least 300. This yields Schnirelmann density at least 1/12 for the same shared sumset, then Mann's theorem yields 24 odd primes plus 3. This is a refinement of an existing formalized elementary method, not a new proof of weak Goldbach.
-- source:
--   Adaptation of xuanji, accepted Prove2Me proof fe1655c0-3df0-4ef3-8e56-89782f953b2e of theorem c7a1b70a-16d7-43a2-bc52-30bca8c7b2af, and middle/large range proofs de0e3352-1dea-42c0-bf16-bd001cb447cd and b31b7a75-b900-487b-968d-4e8324ba386d (6 October 2026). New exact interval certificates and quartic arithmetic, 24 October 2026. Underlying method: Riesel and Vaughan, On sums of primes, Ark. Mat. 21 (1983), sections 7-8; Schnirelmann density and Mann's theorem.

import Mathlib

theorem OAI.OddGoldbach.odd_sum_le_25_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 25 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by sorry
