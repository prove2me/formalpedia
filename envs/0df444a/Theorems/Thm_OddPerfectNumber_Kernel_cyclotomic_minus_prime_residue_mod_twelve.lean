-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_cyclotomic_minus_prime_residue_mod_twelve
-- name    : OddPerfectNumber.Kernel.cyclotomic_minus_prime_residue_mod_twelve
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-03T10:58:07.231511+00:00
-- url     : https://prove2.me/theorems/58ee84a9-f76b-4cbc-9605-61fe80096fcf
-- title:
--   A prime dividing p squared minus p plus 1 is a square exactly when it is 1 mod 12
-- statement:
--   For a prime q other than 3 and p dividing p squared minus p plus 1, q is congruent to 1 modulo 12 exactly when 3 divides q minus 1. Since p has multiplicative order 6 modulo q in this situation, this says p is a quadratic residue modulo q exactly when q is 1 modulo 12. Combined with the plus block, which always yields a residue, this locates precisely which incoming prime sources can be excluded.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- If `p` is an odd prime and `q != 3` is a prime dividing `p^2 - p + 1` with
`q != p`, then `q % 12 = 1` exactly when `3` divides `q - 1`.

Equivalently: an element of order `6` in the multiplicative group modulo `q` is a
square exactly when `12` divides `q - 1`.  This is the sharp discriminator between
the two cyclotomic blocks: the plus block always gives a square, and the minus
block gives a square only in the residue class `1 (mod 12)`. -/
theorem cyclotomic_minus_prime_residue_mod_twelve {p q : Nat} (hp : p.Prime) (hp2 : p != 2)
    (hq : q.Prime) (hq3 : q != 3) (hqp : q != p) (hqd : q ∣ p ^ 2 - p + 1) :
    (q % 12 = 1) ↔ (3 ∣ q - 1) := by
  sorry

end OddPerfectNumber.Kernel
