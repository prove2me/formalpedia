-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sigma_source_of_p_is_fourth_power_residue
-- name    : OddPerfectNumber.Kernel.sigma_source_of_p_is_fourth_power_residue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T21:20:41.094986+00:00
-- url     : https://prove2.me/theorems/6ff0e08d-0b61-47fb-ac9f-9563655bdbfc
-- title:
--   A prime supplying the Euler prime in a local divisor sum is a fourth power residue modulo it
-- statement:
--   Let p be a prime congruent to 1 modulo 4, let t be a natural number not divisible by p, and suppose p divides the local divisor sum of t to the power 2e, that is the sum of the first 2e plus one powers of t. Then t raised to the power (p-1)/4 is congruent to 1 modulo p. Indeed the identity (t-1) times that divisor sum equals t to the power 2e+1 minus 1 shows that t to the power 2e+1 is 1 modulo p, so the multiplicative order of t modulo p divides the odd number 2e+1 and is therefore odd; an odd divisor of p-1 divides (p-1)/4. This says t is a fourth power in the multiplicative group modulo p, which is stronger than being a quadratic residue. It is a genuine restriction on every prime of m that supplies p in the second Dris equation, though it does not by itself exclude such a source.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sigma_source_of_p_is_fourth_power_residue {p t e : Nat} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hpt : Not (Dvd.dvd p t))
    (h : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), t ^ i)) :
    (t : ZMod p) ^ ((p - 1) / 4) = 1 := by
  sorry

end OddPerfectNumber.Kernel
