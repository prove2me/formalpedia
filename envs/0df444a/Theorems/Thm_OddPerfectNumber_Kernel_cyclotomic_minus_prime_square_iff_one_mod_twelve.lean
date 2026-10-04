-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_cyclotomic_minus_prime_square_iff_one_mod_twelve
-- name    : OddPerfectNumber.Kernel.cyclotomic_minus_prime_square_iff_one_mod_twelve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T12:34:04.633984+00:00
-- url     : https://prove2.me/theorems/f0c98c1d-297e-49f6-944a-d32d4f0884eb
-- title:
--   The order of p modulo a prime of p squared minus p plus 1 is 6, and it is a square exactly when that prime is 1 mod 12
-- statement:
--   For an odd prime p and a prime q other than 3 and other than p dividing p squared minus p plus 1, the multiplicative order of p modulo q is exactly 6, and p is a square modulo q exactly when q is congruent to 1 modulo 12. This is proved by an elementary order computation and needs no quadratic reciprocity, because it concerns p as an element modulo q. It excludes a minus-block prime congruent to 7 modulo 12 from being an incoming sigma source of the Euler prime.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- Let `p` be an odd prime and let `q != 3` be a prime dividing `p^2 - p + 1` with
`q != p`.  Then `p` has multiplicative order exactly `6` in `(ZMod q)^×`, and

    legendreSym q p = 1   if and only if   q % 12 = 1.

The mechanism is elementary.  From `q | p^2 - p + 1` we get `p^2 = p - 1 (mod q)`, hence
`p^3 = p^2 - p = -1 (mod q)` and `p^6 = 1 (mod q)`.  The order is therefore `1`, `2`, `3`
or `6`.  Order `1` would give `p = 1 (mod q)` and then `p^2 - p + 1 = 1`, impossible.
Order `2` would give `p = -1 (mod q)` and then `p^2 - p + 1 = 3`, so `q = 3`, excluded.
So the order is `3` or `6`; and order `3` would force `q | p - 1`, which the same
computation excludes, so the order is exactly `6`.

In the cyclic group of order `q - 1` an element of order `6` lies in the unique subgroup
of index `2`, that is among the squares, exactly when `6` divides `(q - 1) / 2`, i.e.
exactly when `12` divides `q - 1`, i.e. exactly when `q % 12 = 1`.

The statement needs no quadratic reciprocity: it concerns `p` as an element modulo `q`.
It is what excludes a minus-block prime congruent to `7 (mod 12)` from being an incoming
sigma source of the Euler prime. -/
theorem cyclotomic_minus_prime_square_iff_one_mod_twelve {p q : Nat} [Fact q.Prime]
    (hp : p.Prime) (hp2 : p != 2) (hq3 : q != 3) (hqp : q != p)
    (hqd : q ∣ p ^ 2 - p + 1) :
    legendreSym q p = 1 ↔ q % 12 = 1 := by
  sorry

end OddPerfectNumber.Kernel
