-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_two_prime_odd_mult_unique_of_non_square
-- name    : OddPerfectNumber.Kernel.two_prime_odd_mult_unique_of_non_square
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T15:21:21.468685+00:00
-- url     : https://prove2.me/theorems/2618ea86-c216-44ab-b47c-3d248a4aeeed
-- title:
--   A non-square block has exactly one odd-multiplicity prime
-- statement:
--   In the square relation y^2 = q*r*a*b with gcd a b = 1 and distinct primes q and r, if a is not a square then exactly one prime t has odd multiplicity in a, and every other prime has even multiplicity. Equivalently, a = t * x^2 for that unique t, with t one of q, r.
-- source:
--   Odd Perfect Number Conjecture, k=5 branch, two-prime parity chain. Every prime with odd multiplicity in `a` lies in `{q, r}` by the accepted child `two_prime_odd_multiplicity_primes_of_a` (89d076b4-d7b5-4a1d-a263-55ad181d1569). The odd-multiplicity support of `a` is nonempty because `a` is not a square (`odd_mult_prime_exists`, ffeb6765-ce67-43db-a9b6-5073e23eccdf). When the sibling block `b` is also not a square the support is confined to the two-element set `{q, r}`, so it is a singleton; this is exactly the counting used in the accepted `two_prime_defects_are_q_and_r` (94301dcb-06a5-4ae5-8b7b-8de0c6c2fcbe). This child isolates that uniqueness for `a` alone, which is what the accepted reconstruction child `odd_mult_single_gives_prime_mul_sq` (35444907-b211-445c-9a63-c2b9f0e4d490) needs in order to rebuild `a = t * x^2`. No new mathematics.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem two_prime_odd_mult_unique_of_non_square {a b q r : Nat} (ha0 : a != 0) (hb0 : b != 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q != r)
    (hsq : exists y : Nat, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y : Nat, y ^ 2 = a) :
    exists t : Nat, t.Prime /\ ¬ Even (a.factorization t) /\
      (forall z : Nat, z != t -> Even (a.factorization z)) := by
  sorry

end OddPerfectNumber.Kernel
