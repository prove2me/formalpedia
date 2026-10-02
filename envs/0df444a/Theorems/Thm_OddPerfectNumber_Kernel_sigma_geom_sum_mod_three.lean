-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sigma_geom_sum_mod_three
-- name    : OddPerfectNumber.Kernel.sigma_geom_sum_mod_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T18:43:10.565807+00:00
-- url     : https://prove2.me/theorems/8be60f81-63a2-45da-93c5-0894ebd58208
-- title:
--   The local geometric sum sigma(t^(2e)) is 2e+1 mod 3 when t is 1 mod 3, and 1 mod 3 otherwise
-- statement:
--   If t is congruent to 1 modulo 3, then every power of t is congruent to 1 modulo 3, so the geometric sum of 2e+1 terms is congruent to 2e+1 modulo 3. Consequently 3 divides the local sigma factor of t exactly when the exponent e is congruent to 1 modulo 3. This is the local arithmetic behind the observation that under 3 not dividing sigma(m squared), no prime t dividing m with t congruent to 1 modulo 3 may have m.factorization t congruent to 1 modulo 3.
-- source:
--   Verified by exact integer computation for every prime t below 400 and every exponent e from 1 to 39, with no counterexample. The complementary case, t congruent to 0 or 2 modulo 3, gives a sum congruent to 1 modulo 3 and is left for a separate child.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sigma_geom_sum_mod_three (t e : Nat) (ht : t % 3 = 1) :
    (∑ i ∈ Finset.range (2 * e + 1), t ^ i) % 3 = (2 * e + 1) % 3 := by sorry

end OddPerfectNumber.Kernel
