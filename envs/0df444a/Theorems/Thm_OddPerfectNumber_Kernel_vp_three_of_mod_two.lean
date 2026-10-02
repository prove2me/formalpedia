-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_vp_three_of_mod_two
-- name    : OddPerfectNumber.Kernel.vp_three_of_mod_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T15:45:10.140228+00:00
-- url     : https://prove2.me/theorems/8822a094-7dd3-440c-98fa-fe168e837009
-- title:
--   The 3-adic multiplicity of n^2-n+1 is exactly 1 when n is 2 mod 3
-- statement:
--   If n is congruent to 2 modulo 3, then the exponent of 3 in n^2-n+1 is exactly one. Writing n = 3k+2 gives n^2-n+1 = 3(3k^2+3k+1), and the bracket is congruent to 1 modulo 3, so no further factor of 3 occurs.
-- source:
--   The companion 3-adic entry to vp_three_of_mod_one, needed by the two-prime squarefree-index residual. Verified by exact integer computation for every n <= 30000 in the residue class n % 3 = 2, with no counterexample.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem vp_three_of_mod_two (n : Nat) (hn : n % 3 = 2) :
    (n ^ 2 - n + 1).factorization 3 = 1 := by sorry

end OddPerfectNumber.Kernel
