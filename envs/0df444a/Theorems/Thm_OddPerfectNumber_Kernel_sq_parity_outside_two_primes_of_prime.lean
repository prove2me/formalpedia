-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sq_parity_outside_two_primes_of_prime
-- name    : OddPerfectNumber.Kernel.sq_parity_outside_two_primes_of_prime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T20:53:49.315075+00:00
-- url     : https://prove2.me/theorems/bf06b2fb-6247-4217-867d-3b568bad00c9
-- title:
--   A square times a square times q times r forces even multiplicity of a prime outside q and r
-- statement:
--   Let X, d1, q, r and l be natural numbers, with X and d1 nonzero, and let l be a prime dividing neither q nor r. If X times d1 squared times q times r is a perfect square, then l occurs in X to an even multiplicity. The left-hand side being a square forces an even multiplicity for every prime in the product; the contribution of d1 squared is twice the multiplicity of d1 and so is already even; and the contribution of q times r is supported on q and r only, so it vanishes at the prime l. Subtracting leaves the multiplicity in X even. This is the squareclass step underlying the two-prime residual, where it says that the odd-multiplicity prime support of the cyclotomic part is exactly the pair q and r. The primality of l is essential: without it the claim is false, for instance l = 6, q = 2, r = 3, d1 = 1, X = 6 gives 6 times 1 times 6 equal to the square 36 while 6 occurs in 6 to the odd multiplicity one.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sq_parity_outside_two_primes_of_prime {X d1 q r l : Nat}
    (hX0 : X != 0) (hd10 : d1 != 0) (hl : l.Prime)
    (hm2 : X * d1 ^ 2 * (q * r) != 0)
    (hsq : ∃ y : Nat, y ^ 2 = X * d1 ^ 2 * (q * r))
    (hlq : Not (Dvd.dvd l q)) (hlr : Not (Dvd.dvd l r)) :
    Even (X.factorization l) := by
  sorry

end OddPerfectNumber.Kernel
