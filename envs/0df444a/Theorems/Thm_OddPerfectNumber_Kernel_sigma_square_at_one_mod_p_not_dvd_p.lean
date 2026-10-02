-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sigma_square_at_one_mod_p_not_dvd_p
-- name    : OddPerfectNumber.Kernel.sigma_square_at_one_mod_p_not_dvd_p
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T21:33:13.688677+00:00
-- url     : https://prove2.me/theorems/272ab56e-9633-4bdb-8c98-cb4fa9409f60
-- title:
--   A prime at least five does not divide the three-term sum at a residue one
-- statement:
--   Let p be a prime at least five, and let t be a natural number with t congruent to 1 modulo p. Then p does not divide 1 + t + t squared. Indeed every power of t is congruent to 1 modulo p, so the three-term sum is congruent to 3 modulo p, and a prime at least five never divides 3. This isolates why the Euler prime cannot be supplied by a prime of exponent one occurring in the two-prime square-free residual: for such a prime the local divisor sum is exactly this three-term sum.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sigma_square_at_one_mod_p_not_dvd_p {p t : Nat} (hp : p.Prime)
    (hp5 : 5 ≤ p) (ht : t % p = 1) :
    Not (Dvd.dvd p (1 + t + t ^ 2)) := by
  sorry

end OddPerfectNumber.Kernel
