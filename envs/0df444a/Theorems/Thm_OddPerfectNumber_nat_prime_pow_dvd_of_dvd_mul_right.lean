-- Prove2me | Theorems.Thm_OddPerfectNumber_nat_prime_pow_dvd_of_dvd_mul_right
-- name    : OddPerfectNumber.nat_prime_pow_dvd_of_dvd_mul_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T01:45:54.945263+00:00
-- url     : https://prove2.me/theorems/ae2bf199-78f7-4131-b1da-727135d37b6a
-- title:
--   Nat prime powers divide the opposite factor when the prime is absent
-- statement:
--   If a power of a natural prime divides a product and the prime does not divide the right factor, that power divides the left factor.
-- source:
--   A small reusable interface to the pinned Mathlib prime-power divisibility lemma.

import Mathlib

namespace OddPerfectNumber

theorem nat_prime_pow_dvd_of_dvd_mul_right (p a b n : Nat)
    (hp : p.Prime) (hnot : ¬ p ∣ b) (hdiv : p ^ n ∣ a * b) :
    p ^ n ∣ a := by
  sorry

end OddPerfectNumber
