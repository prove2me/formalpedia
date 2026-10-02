-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sigma_geom_sum_mod_three_ne_one
-- name    : OddPerfectNumber.Kernel.sigma_geom_sum_mod_three_ne_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T18:42:55.923988+00:00
-- url     : https://prove2.me/theorems/506b363a-d3ed-4177-a5a9-9ac693b3943d
-- title:
--   The local geometric sum sigma(t^(2e)) is 1 mod 3 when t is not 1 mod 3
-- statement:
--   If t is not congruent to 1 modulo 3, then the geometric sum of an odd number 2e+1 of powers of t is congruent to 1 modulo 3. This covers both remaining residue classes: t congruent to 0 modulo 3 gives every positive power congruent to 0 and the sum congruent to 1 from its first term, and t congruent to 2 modulo 3 gives an odd number of alternating 1 and minus 1 terms which sum to 1. Together with the companion child this says that 3 divides a local sigma factor only through the first residue class.
-- source:
--   Verified by exact integer computation for every prime t below 400 and every exponent e from 1 to 39, with no counterexample. This is the complement of sigma_geom_sum_mod_three.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sigma_geom_sum_mod_three_ne_one (t e : Nat) (ht : t % 3 != 1) :
    (∑ i ∈ Finset.range (2 * e + 1), t ^ i) % 3 = 1 := by sorry

end OddPerfectNumber.Kernel
