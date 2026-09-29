-- Prove2me | Theorems.Thm_OddPerfectNumber_four_support_ordered
-- name    : OddPerfectNumber.four_support_ordered
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T13:35:58.590918+00:00
-- url     : https://prove2.me/theorems/8dfbcade-ad0c-4cd4-8364-175d4280fa4b
-- title:
--   Ordered extraction of four prime support elements
-- statement:
--   A natural number with exactly four distinct prime divisors has those divisors represented by four strictly increasing primes.

import Mathlib

theorem OddPerfectNumber.four_support_ordered (m : Nat)
    (hcard : m.primeFactors.card = 4) :
    ∃ q1 q2 q3 q4 : Nat,
      q1.Prime ∧ q2.Prime ∧ q3.Prime ∧ q4.Prime ∧
      q1 < q2 ∧ q2 < q3 ∧ q3 < q4 ∧
      m.primeFactors = {q1, q2, q3, q4} := by sorry
