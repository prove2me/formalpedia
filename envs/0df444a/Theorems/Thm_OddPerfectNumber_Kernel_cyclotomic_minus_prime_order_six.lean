-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_cyclotomic_minus_prime_order_six
-- name    : OddPerfectNumber.Kernel.cyclotomic_minus_prime_order_six
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T19:04:13.562784+00:00
-- url     : https://prove2.me/theorems/d1c537a6-c3bc-48d6-9a94-d3ca6ac01d3f
-- title:
--   A prime other than 3 dividing p squared minus p plus 1 sees p of order exactly six
-- statement:
--   For an odd prime p and a prime q other than 3 and other than p that divides p squared minus p plus 1, the multiplicative order of p modulo q is exactly 6. The order cannot be 1, because that would make p squared minus p plus 1 equal 1; cannot be 2, because that would force q to be 3; and cannot be 3, because that would force q to divide both cyclotomic blocks and hence to be 2.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- Let `p` be an odd prime and let `q != 3` be a prime dividing `p^2 - p + 1` with
`q != p`.  Then `orderOf (p : ZMod q) = 6`.

Mechanism: `q | p^2 - p + 1` gives `p^2 = p - 1`, hence `p^3 = -1` and `p^6 = 1`, so the
order divides `6`.  Order `1` would give `p^2 - p + 1 = 1`, impossible.  Order `2` would give
`p = -1 (mod q)`, hence `p^2 - p + 1 = 3` and `q = 3`, excluded.  Order `3` would force
`q | p^2 + p + 1` as well, hence `q | 2p`, and `q != p` gives `q | 2`, so `q = 2`, impossible
because `p^2 - p + 1` is odd.  Hence the order is `6`. -/
theorem cyclotomic_minus_prime_order_six {p q : Nat} [Fact q.Prime]
    (hp : p.Prime) (hp2 : p != 2) (hq : q.Prime) (hq3 : q != 3) (hqp : q != p)
    (hqd : q ∣ p ^ 2 - p + 1) :
    orderOf (p : ZMod q) = 6 := by
  sorry

end OddPerfectNumber.Kernel
