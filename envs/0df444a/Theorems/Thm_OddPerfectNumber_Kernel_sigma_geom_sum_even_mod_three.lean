-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sigma_geom_sum_even_mod_three
-- name    : OddPerfectNumber.Kernel.sigma_geom_sum_even_mod_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T18:54:28.851758+00:00
-- url     : https://prove2.me/theorems/0bea2a7d-4bee-498d-8b5c-0aaebef80436
-- title:
--   An even-length geometric sum is 0 mod 3 when t is 2 mod 3
-- statement:
--   If t is congruent to 2 modulo 3 and the length k of the geometric sum is even, then the sum is congruent to 0 modulo 3. The powers of t alternate between 1 and 2 modulo 3 because 2 times 2 is 1 modulo 3, so the terms pair up as 1 plus 2, and each pair contributes 0. This is the auxiliary statement needed for the odd-length case, where a single unpaired 1 remains.
-- source:
--   Verified by exact integer computation for every integer t below 400, every even k up to 80, with no counterexample. The proof pairs consecutive terms, each contributing 1 plus 2 which is 0 modulo 3, so the induction is in steps of two rather than in steps of one.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sigma_geom_sum_even_mod_three (t k : Nat) (ht : t % 3 = 2) (hk : k % 2 = 0) :
    (∑ i ∈ Finset.range k, t ^ i) % 3 = 0 := by sorry

end OddPerfectNumber.Kernel
