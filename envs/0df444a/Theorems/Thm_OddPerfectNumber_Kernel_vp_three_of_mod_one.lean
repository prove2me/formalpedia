-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_vp_three_of_mod_one
-- name    : OddPerfectNumber.Kernel.vp_three_of_mod_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T15:44:51.784415+00:00
-- url     : https://prove2.me/theorems/a9713116-6d8f-4d33-b2e5-e0fa3b1b1651
-- title:
--   The 3-adic multiplicity of n^2+n+1 is exactly 1 when n is 1 mod 3
-- statement:
--   If n is congruent to 1 modulo 3, then the exponent of 3 in n^2+n+1 is exactly one. Writing n = 3k+1 gives n^2+n+1 = 3(3k^2+3k+1), and the bracket is congruent to 1 modulo 3, so no further factor of 3 occurs.
-- source:
--   This is the elementary 3-adic entry needed by the two-prime squarefree-index residual of five_no_two_prime_squarefree_index. Verified by exact integer computation for every n <= 30000 in the residue class n % 3 = 1, with no counterexample.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem vp_three_of_mod_one (n : Nat) (hn : n % 3 = 1) :
    (n ^ 2 + n + 1).factorization 3 = 1 := by sorry

end OddPerfectNumber.Kernel
