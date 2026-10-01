-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_odd_mult_single_gives_prime_mul_sq
-- name    : OddPerfectNumber.Kernel.odd_mult_single_gives_prime_mul_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T14:32:32.168745+00:00
-- url     : https://prove2.me/theorems/35444907-b211-445c-9a63-c2b9f0e4d490
-- title:
--   A single odd-multiplicity prime forces prime times a square
-- statement:
--   If a nonzero natural number a has exactly one prime t with odd multiplicity in its factorization, then a = t*x^2 for some x.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem odd_mult_single_gives_prime_mul_sq {a t : Nat} (ha0 : a != 0) (ht : t.Prime)
    (ht0 : ! Even (a.factorization t))
    (hall : forall z : Nat, z != t -> Even (a.factorization z)) :
    exists y : Nat, a = t * y ^ 2 := by
  sorry

end OddPerfectNumber.Kernel
