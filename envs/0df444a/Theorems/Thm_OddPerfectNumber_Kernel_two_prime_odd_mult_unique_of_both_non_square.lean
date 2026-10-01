-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_two_prime_odd_mult_unique_of_both_non_square
-- name    : OddPerfectNumber.Kernel.two_prime_odd_mult_unique_of_both_non_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T15:24:49.661671+00:00
-- url     : https://prove2.me/theorems/4308037b-5f4a-4a25-ad4f-1630244757b0
-- title:
--   With both blocks non-square, each has a unique odd-multiplicity prime
-- statement:
--   In the square relation y^2 = q*r*a*b with gcd a b = 1, distinct primes q and r, and neither a nor b a square, exactly one prime t has odd multiplicity in a, and every other prime has even multiplicity. Equivalently a = t * x^2 for that unique t, which is one of q and r.
-- source:
--   Odd Perfect Number Conjecture, k=5 branch, two-prime parity chain. Every prime with odd multiplicity in `a` lies in `{q, r}` by the accepted `two_prime_odd_multiplicity_primes_of_a` (89d076b4-d7b5-4a1d-a263-55ad181d1569), and a non-square `a` has an odd-multiplicity prime by `odd_mult_prime_exists` (ffeb6765-ce67-43db-a9b6-5073e23eccdf). The counting step is the accepted `two_prime_defects_are_q_and_r` (94301dcb-06a5-4ae5-8b7b-8de0c6c2fcbe): the odd supports of `a` and `b` are disjoint by `gcd a b = 1`, both nonempty, and both contained in the two-element set `{q, r}`, so both are singletons. This child isolates the singleton for `a`, the input the accepted reconstruction child `odd_mult_single_gives_prime_mul_sq` (35444907-b211-445c-9a63-c2b9f0e4d490) needs to rebuild `a = t * x^2`. No new mathematics. NOTE: the sibling `two_prime_odd_mult_unique_of_non_square` (2618ea86-c216-44ab-b47c-3d248a4aeeed) omits `hnb` and is FALSE: with `q = 5`, `r = 7`, `a = 35`, `b = 1` the hypotheses hold (`5*7*35*1 = 1225 = 35^2`, `gcd 35 1 = 1`, `35` is not a square) yet `a` has two odd-multiplicity primes, 5 and 7.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem two_prime_odd_mult_unique_of_both_non_square {a b q r : Nat} (ha0 : a != 0) (hb0 : b != 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q != r)
    (hsq : exists y : Nat, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y : Nat, y ^ 2 = a)
    (hnb : ¬ ∃ y : Nat, y ^ 2 = b) :
    exists t : Nat, t.Prime /\ ¬ Even (a.factorization t) /\
      (forall z : Nat, z != t -> Even (a.factorization z)) := by
  sorry

end OddPerfectNumber.Kernel
