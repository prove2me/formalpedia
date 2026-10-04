-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_cyclotomic_plus_prime_order_three
-- name    : OddPerfectNumber.Kernel.cyclotomic_plus_prime_order_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T19:04:06.036624+00:00
-- url     : https://prove2.me/theorems/c3b04446-f3cf-429e-9e6a-019378ad8b84
-- title:
--   A prime other than 3 dividing p squared plus p plus 1 at odd multiplicity sees p of order exactly three
-- statement:
--   For an odd prime p and a prime q other than 3 that divides p squared plus p plus 1, the multiplicative order of p modulo q is exactly 3, so p is a square modulo q. This is the exact dual of the minus-block statement, in which the order is 6 and p is a square exactly when q is 1 modulo 12. Together they are the sharp test distinguishing the two cyclotomic blocks.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- Let `p` be an odd prime and let `q != 3` be a prime dividing `p^2 + p + 1`.  Then
`orderOf (p : ZMod q) = 3`.

Mechanism: `p^3 - 1 = (p - 1) (p^2 + p + 1)` gives `p^3 = 1 (mod q)`, and `q != p` because
`p | p^2 + p + 1` would give `p | 1`.  So the order divides `3`.  Order `1` means
`p = 1 (mod q)`, whence `p^2 + p + 1 = 3` and `q = 3`, excluded.  Hence the order is `3`.

Combined with the Proved `cyclotomic_plus_prime_is_quadratic_residue` (4bd3c06a), this says
`p` is a QUADRATIC RESIDUE modulo `q`, so by reciprocity it is also a residue modulo a `p`
with `p % 4 = 1`.  That is precisely why the plus-block defect prime is NOT excluded as an
incoming sigma source of the Euler prime, and it is the exact dual of
`cyclotomic_minus_prime_square_iff_one_mod_twelve` (f0c98c1d). -/
theorem cyclotomic_plus_prime_order_three {p q : Nat} [Fact q.Prime]
    (hp : p.Prime) (hp2 : p != 2) (hq : q.Prime) (hq3 : q != 3)
    (hqd : q ∣ p ^ 2 + p + 1) :
    orderOf (p : ZMod q) = 3 := by
  sorry

end OddPerfectNumber.Kernel
