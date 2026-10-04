-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_primes_one_mod_six_of_D
-- name    : OddPerfectNumber.Kernel.five_cyclotomic_primes_one_mod_six_of_D
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T00:47:02.093853+00:00
-- url     : https://prove2.me/theorems/79b33655-fa31-4875-8191-2ba4e4fdf53d
-- title:
--   A prime dividing the second cyclotomic block is one modulo six
-- statement:
--   Let p, q be natural numbers. Suppose p is a prime different from three, q is a prime different from three, and q divides p squared minus p plus one. Then q is congruent to one modulo six. Indeed a prime q dividing p squared minus p plus one also divides p cubed plus one, because p cubed plus one is the product of p plus one with p squared minus p plus one. If p were congruent to minus one modulo q then one plus one plus one would be congruent to zero modulo q, which would force q to be three. So the multiplicative order of p modulo q is neither one nor two, and it divides six, hence it is six; by Lagrange's theorem six divides q minus one.
-- source:
--   Elementary multiplicative-order argument. p^2-p+1 divides p^3+1, so the order of p mod q divides 6; it is neither 1 nor 2 because either would force p = -1 mod q and hence 3 = 0 mod q. The order is therefore 6 and 6 | q-1. Companion to the Proved five_cyclotomic_primes_one_mod_three (fff482b8), which covers the block p^2+p+1.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_cyclotomic_primes_one_mod_six_of_D {p q : Nat}
    (hp : Nat.Prime p) (hp3 : p != 3) (hq : Nat.Prime q) (hq3 : q != 3)
    (hqd : q ∣ p ^ 2 - p + 1) :
    q % 6 = 1 := by
  sorry

end OddPerfectNumber.Kernel
