-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_square_witness_of_first_dris
-- name    : OddPerfectNumber.Kernel.square_witness_of_first_dris
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T19:02:53.571284+00:00
-- url     : https://prove2.me/theorems/ba579ec6-48d8-4a65-97cd-f8037b5ee921
-- title:
--   The first k=5 Dris equation makes q*r times the cyclotomic blocks a square
-- statement:
--   From the first k=5 Dris equation alone, the product q*r*(p^2+p+1)*((p+1)/2*(p^2-p+1)) is a perfect square. Cancelling the factor 2 gives m^2 = d1^2 * S with S that product; m odd forces m != 0 hence d1 != 0, and S is positive since q, r are prime and the cyclotomic blocks are positive; square cancellation then yields IsSquare S. This is exactly the hsq hypothesis required by five_two_prime_cyclotomic_primes_dvd_m.
-- source:
--   Bridge child for the k=5 two-prime residual: supplies hsq to 13f23023. Proof route: cancel 2 from h1 (explicit positivity side-goal), d1 != 0 from Odd m, S positivity from primality, then isSquare_of_sq_mul_eq_sq.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem square_witness_of_first_dris
    (p m d1 q r : Nat)
    (hp : p.Prime) (hp2 : p != 2)
    (hm : Odd m)
    (hq : q.Prime) (hr : r.Prime)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r))) :
    exists y : Nat,
      y ^ 2 = q * r * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) := by
  sorry

end OddPerfectNumber.Kernel
