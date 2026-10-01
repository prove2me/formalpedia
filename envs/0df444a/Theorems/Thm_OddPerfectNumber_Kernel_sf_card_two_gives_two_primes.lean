-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sf_card_two_gives_two_primes
-- name    : OddPerfectNumber.Kernel.sf_card_two_gives_two_primes
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T21:44:29.902988+00:00
-- url     : https://prove2.me/theorems/c4e30275-a3b1-4518-a2ad-aeff964d237b
-- title:
--   A squarefree natural with exactly two prime factors is a product of two distinct primes
-- statement:
--   Let $d$ be a positive squarefree natural with exactly two distinct prime factors. Then $d$ is the product of two distinct primes $q < r$.
--
--   This is the standard characterisation used to reduce a failure of $\omega(d) \ge 3$ to an explicit two-prime kernel: combined with `Nat.squarefree_and_primeFactors_card_eq_two_iff` it pins the exact orientation $d = q r$ with $q < r$ both prime, which is the shape the $k = 5$ residual needs before the second Dris equation can be brought to bear. It is a thin wrapper over the pinned Mathlib theorem and encodes no unproved conjecture.
-- source:
--   Mathlib/Data/Nat/Squarefree.lean (Nat.squarefree_and_primeFactors_card_eq_two_iff, Nat.prod_primeFactors_of_squarefree) and Mathlib/Data/Nat/Factorization.lean (Nat.prime_of_mem_primeFactors). A thin structural wrapper over pinned Mathlib; it encodes no unproved conjecture.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sf_card_two_gives_two_primes {d : Nat} (hd0 : 0 < d) (hdsf : Squarefree d)
    (hcard : d.primeFactors.card = 2) :
    exists q r : Nat, q < r /\ q.Prime /\ r.Prime /\ d = q * r := by
  sorry

end OddPerfectNumber.Kernel
