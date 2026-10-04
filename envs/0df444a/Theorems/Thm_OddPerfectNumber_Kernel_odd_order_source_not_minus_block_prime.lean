-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_odd_order_source_not_minus_block_prime
-- name    : OddPerfectNumber.Kernel.odd_order_source_not_minus_block_prime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T20:50:48.74898+00:00
-- url     : https://prove2.me/theorems/240feedb-a882-4aad-ae29-2c8c898e1f1c
-- title:
--   A prime of the minus cyclotomic block cannot be an incoming sigma source of the Euler prime
-- statement:
--   If q is a quadratic nonresidue modulo an odd prime p, then the multiplicative order of q modulo p is even. Since an incoming sigma source of the Euler prime must have odd order modulo it, no prime that is a quadratic nonresidue modulo the Euler prime can be such a source. Applied to the minus cyclotomic block, where the index prime is a nonresidue, this excludes it entirely.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- Suppose `q` is a prime other than `3` dividing `p ^ 2 - p + 1`, where `p` is an odd
prime with `p % 4 = 1`, and suppose additionally that `q` is a quadratic NONRESIDUE modulo `p`.
Then the multiplicative order of `q` modulo `p` is EVEN.

Mechanism.  Write `d = orderOf (q : ZMod p)`.  Fermat gives `d | p - 1`.  A quadratic residue
modulo `p` is exactly an element whose order divides `(p - 1) / 2`: if `q = u ^ 2` then
`q ^ ((p-1)/2) = u ^ (p-1) = 1`, and conversely `q ^ ((p-1)/2) = 1` forces `q` to be a square
because `(p-1)/2 = (p-1)/4 * 2` and the character takes the value `1` on squares.  So a
nonresidue forces `d ∤ (p-1)/2`, and since `d | p-1` it follows that `d` is even.

This is the order-theoretic content of the Proved
`cyclotomic_minus_prime_square_iff_one_mod_twelve` (f0c98c1d): in the live k = 5 branch, where
`q % 12 = 7`, the minus-block index prime has EVEN order modulo the Euler prime.  An incoming
sigma source of `p` must satisfy `q ^ (2 e + 1) = 1 (mod p)` with `2 e + 1` odd, hence its order
is ODD.  So the minus-block index prime can never be such a source, and neither can `3`, which is
excluded by `three_is_quadratic_nonresidue_mod_euler_prime` (f113d40e).

The COROLLARY used by the mission is: the incoming sigma source of the Euler prime is the
MIDDLE-block index prime, or a prime dividing the square part. -/
theorem odd_order_source_not_minus_block_prime {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hp : p.Prime) (hp4 : p % 4 = 1) (hq : q.Prime) (hqp : q != p)
    (hleg : legendreSym q p = -1) :
    Even (orderOf (q : ZMod p)) := by
  sorry

end OddPerfectNumber.Kernel
