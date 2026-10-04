-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_cyclotomic_minus_prime_is_one_mod_three
-- name    : OddPerfectNumber.Kernel.cyclotomic_minus_prime_is_one_mod_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T11:04:58.110986+00:00
-- url     : https://prove2.me/theorems/78e2bdfb-fc99-4093-b611-b95a71e98fed
-- title:
--   A prime other than 3 dividing p squared minus p plus 1 is 1 mod 3
-- statement:
--   For an odd prime p, any prime q other than 3 that divides p squared minus p plus 1 satisfies q congruent to 1 modulo 3. This is the minus-block analogue of the proved plus-block statement and is what restricts the two odd-multiplicity index primes to the residue classes 1 and 7 modulo 12.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- The minus-block counterpart of `five_cyclotomic_primes_one_mod_three` (fff482b8).

If `p` is an odd prime and `q != 3` is a prime dividing `p^2 - p + 1`, then
`q % 3 = 1`.  Together with `q` being an odd prime this gives `q % 6 = 1`, so
`3` divides `q - 1` and the order-`6` element `p` modulo `q` lies in the subgroup
of index `2` precisely when `12` divides `q - 1`. -/
theorem cyclotomic_minus_prime_is_one_mod_three {p q : Nat} (hp : p.Prime) (hp2 : p != 2)
    (hq : q.Prime) (hq3 : q != 3) (hqd : q ∣ p ^ 2 - p + 1) :
    q % 3 = 1 := by
  sorry

end OddPerfectNumber.Kernel
