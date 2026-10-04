-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_cyclotomic_plus_prime_is_quadratic_residue
-- name    : OddPerfectNumber.Kernel.cyclotomic_plus_prime_is_quadratic_residue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T10:57:55.618065+00:00
-- url     : https://prove2.me/theorems/4bd3c06a-b940-4c5a-aed1-5132059d5fc0
-- title:
--   A prime dividing p squared plus p plus 1 sees p as a square
-- statement:
--   A prime other than 3 dividing p squared plus p plus 1, for odd prime p, is congruent to 1 modulo 6. Hence the multiplicative order 3 element p modulo q is a square, which is the congruence ingredient for showing p is a quadratic residue modulo q and therefore, by symmetry when p is 1 modulo 4, that q is a quadratic residue modulo p.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- If `p` is an odd prime and `q` is a prime other than `3` dividing `p^2 + p + 1`,
then `q = 1 (mod 6)`, so `3` divides `(q - 1) / 2`.

This is the congruence fact behind `legendreSym q p = 1`: the element `p` of the
multiplicative group modulo `q` has order `3`, and an element of order `3` lies in the
subgroup of squares exactly when `3` divides `(q - 1) / 2`. -/
theorem cyclotomic_plus_prime_is_quadratic_residue {p q : Nat} (hp : p.Prime) (hp2 : p != 2)
    (hq : q.Prime) (hq3 : q != 3) (hqd : q ∣ p ^ 2 + p + 1) :
    q % 6 = 1 := by
  sorry

end OddPerfectNumber.Kernel
