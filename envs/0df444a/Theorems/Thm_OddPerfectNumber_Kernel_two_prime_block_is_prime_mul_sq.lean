-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_two_prime_block_is_prime_mul_sq
-- name    : OddPerfectNumber.Kernel.two_prime_block_is_prime_mul_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T15:07:02.437221+00:00
-- url     : https://prove2.me/theorems/672c3afb-a666-41e5-b792-996d5d5db518
-- title:
--   Each coprime block of the two-prime square is a prime times a square
-- statement:
--   Suppose y^2 = q*r*a*b with gcd a b = 1, distinct primes q and r, and neither a nor b a square. Then a is a prime times a square, and that prime is one of q, r.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem two_prime_block_is_prime_mul_sq {a b q r : Nat} (ha0 : a != 0) (hb0 : b != 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q != r)
    (hsq : exists y : Nat, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y : Nat, y ^ 2 = a)
    (hnb : ¬ ∃ y : Nat, y ^ 2 = b) :
    exists t x : Nat, t.Prime /\ a = t * x ^ 2 /\ (t = q \/ t = r) := by
  sorry

end OddPerfectNumber.Kernel
