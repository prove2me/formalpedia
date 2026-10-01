-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_exists_odd_factorization_prime_of_mul_ne_even
-- name    : OddPerfectNumber.Kernel.exists_odd_factorization_prime_of_mul_ne_even
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T07:16:12.541683+00:00
-- url     : https://prove2.me/theorems/259d71b5-76cb-4936-a7e1-ecec332a8ca3
-- title:
--   An odd multiplicity in a product forces an odd multiplicity in one factor
-- statement:
--   Let a and b be nonzero natural numbers and let p be a prime. If p occurs to an odd multiplicity in the product a times b, then p occurs to an odd multiplicity in at least one of the two factors. This is the step that turns an odd total p-adic valuation of the divisor sum of m squared into the existence of a particular local sigma source carrying an odd p-adic valuation: a product whose two factors both have even multiplicity at p has an even multiplicity at p.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem exists_odd_factorization_prime_of_mul_ne_even {a b p : Nat}
    (ha : a != 0) (hb : b != 0) (hp : p.Prime)
    (hodd : Not (Even ((a * b).factorization p))) :
    Not (Even (a.factorization p)) \/ Not (Even (b.factorization p)) := by
  sorry

end OddPerfectNumber.Kernel
