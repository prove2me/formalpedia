-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_cyclotomic_plus_prime_residue_mod_euler
-- name    : OddPerfectNumber.Kernel.cyclotomic_plus_prime_residue_mod_euler
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T19:42:20.832213+00:00
-- url     : https://prove2.me/theorems/8c50fd63-c5f2-4d79-a308-58e84177a620
-- title:
--   A prime of the plus cyclotomic block is a quadratic residue modulo the Euler prime
-- statement:
--   If p is a prime congruent to 1 modulo 4 and q is a prime other than 3 dividing p squared plus p plus 1, then q is a quadratic residue modulo p. The reason is that p has multiplicative order exactly 3 modulo q, which is odd and hence makes p a square modulo q, and quadratic reciprocity transfers this back because p is 1 modulo 4. Together with the proved minus-block statement this sharpens the two cyclotomic block primes: the middle-block prime may be an incoming sigma source of the Euler prime, the minus-block prime may not.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- The exact dual of `cyclotomic_minus_prime_square_iff_one_mod_twelve` (f0c98c1d).

Let `p` be an odd prime, let `q != 3` be a prime with `q` dividing `p ^ 2 + p + 1`, and
assume `p % 4 = 1`.  Then `q` is a QUADRATIC RESIDUE modulo `p`.

Mechanism, in two halves.

* `q | p^2 + p + 1` gives `p^3 = 1 (mod q)`, so the order of `p` modulo `q` divides `3` and
  is odd.  Since `q != 3`, the order cannot be `1` (that would force `p^2 + p + 1 = 3`), hence
  it is exactly `3`.  An element of odd order in a finite field of characteristic `!= 2` is a
  square, so `p` is a quadratic residue modulo `q`.
* Quadratic reciprocity transfers it: because `p % 4 = 1` the two signs agree, so `q` is a
  quadratic residue modulo `p` as well.

This is precisely why the MIDDLE-block defect prime `q` is NOT excluded as an incoming sigma
source of the Euler prime, while the MINUS-block prime `r` IS excluded by f0c98c1d.  The two
block primes are thus sharply distinguished by quadratic residuosity, and the asymmetry is the
structural handle on the two-prime kernel. -/
theorem cyclotomic_plus_prime_residue_mod_euler {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hq3 : q != 3)
    (hqd : q ∣ p ^ 2 + p + 1) :
    legendreSym q p = 1 := by
  sorry

end OddPerfectNumber.Kernel
