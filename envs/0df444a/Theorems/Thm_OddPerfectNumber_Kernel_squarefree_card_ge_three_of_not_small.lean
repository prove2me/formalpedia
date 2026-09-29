-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_squarefree_card_ge_three_of_not_small
-- name    : OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T00:22:20.700479+00:00
-- url     : https://prove2.me/theorems/64627c09-9af1-4ab3-afc0-a3498abf1dc3
-- title:
--   A square-free number that is not 1, a prime, or a semiprime has at least three prime factors
-- statement:
--   Let $d$ be a positive square-free natural number. If $d$ is not $1$, not a prime, and not a product of two distinct primes $q \cdot r$ with $q < r$ both prime, then $d$ has at least three distinct prime factors. This is the purely combinatorial counting step used to turn 'the square-free part of the Dris index is not 1, not prime, and not a semiprime' into a lower bound of 3 on $\#\mathrm{primeFactors}$. The proof is a three-way case split on $\#\mathrm{primeFactors}$ using $\mathrm{prod\_primeFactors\_of\_squarefree}$.
-- source:
--   Elementary counting helper for the k=5 square-free-index reduction of the Odd Perfect Number Conjecture; the square-free part $d_2$ of the Dris index satisfies $\omega(d_2) \ge 3$ once $d_2 = 1$, $d_2$ prime, and $d_2 = q r$ are each excluded.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem squarefree_card_ge_three_of_not_small {d : Nat} (hdpos : 0 < d) (hdsf : Squarefree d) (hne1 : d ≠ 1) (hnePrime : ∀ q, q.Prime → d ≠ q) (hneTwo : ∀ q r, q.Prime → r.Prime → q < r → d ≠ q * r) :
    3 ≤ d.primeFactors.card := by
  sorry

end OddPerfectNumber.Kernel
