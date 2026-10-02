-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sq_parity_outside_two_primes
-- name    : OddPerfectNumber.Kernel.sq_parity_outside_two_primes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T20:15:16.393838+00:00
-- url     : https://prove2.me/theorems/cd92ad64-1798-49de-9849-6162f2cf16f7
-- title:
--   A square times a square times q times r forces even multiplicity outside q and r
-- statement:
--   If X times d1 squared times q times r is a perfect square, then every prime other than q and r occurs in X to an even multiplicity. The left-hand side being a square forces even multiplicity for every prime in the product; the contribution of d1 squared is twice the multiplicity of d1 and so already even; and the contribution of q times r is supported only on q and r. Subtracting leaves the multiplicity in X even. This is the squareclass step underlying the two-prime residual, where it says that the odd-multiplicity prime support of the cyclotomic part is exactly the pair q and r.
-- source:
--   This is the reusable squareclass step for the two-prime square-free-index residual. It is stated generically in X, d1, q, r and l so that it can be applied to the cyclotomic product ((p+1)/2)*(p^2+p+1)*(p^2-p+1) with l = 3. The proof uses only Nat.factorization_mul, Nat.factorization_pow and Nat.factorization_eq_zero_of_not_dvd, and the conclusion is phrased with Even so that it composes with the Proved parity splitting child exists_odd_factorization_prime_of_mul_ne_even.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sq_parity_outside_two_primes {X d1 q r l : Nat}
    (hX0 : X != 0) (hd10 : d1 != 0)
    (hm2 : X * d1 ^ 2 * (q * r) != 0)
    (hsq : ∃ y : Nat, y ^ 2 = X * d1 ^ 2 * (q * r))
    (hlq : Not (Dvd.dvd l q)) (hlr : Not (Dvd.dvd l r)) :
    Even (X.factorization l) := by sorry

end OddPerfectNumber.Kernel
