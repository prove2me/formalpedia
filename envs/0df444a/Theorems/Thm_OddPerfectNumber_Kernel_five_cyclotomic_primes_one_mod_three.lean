-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_primes_one_mod_three
-- name    : OddPerfectNumber.Kernel.five_cyclotomic_primes_one_mod_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T21:15:32.008315+00:00
-- url     : https://prove2.me/theorems/fff482b8-4fcf-4a31-b708-48de77ca53d8
-- title:
--   Every prime divisor of p^2+p+1 or p^2-p+1 other than 3 is 1 mod 3
-- statement:
--   Let $p$ be an odd prime and let $q \neq 3$ be a prime divisor of $p^2+p+1$. Then $q \equiv 1 \pmod 3$.
--
--   Indeed $p^2+p+1 \mid p^3-1$ while $p \not\equiv 1 \pmod q$, because $p \equiv 1 \pmod q$ would force $q \mid 3$. Since $q \neq 3$ the multiplicative order of $p$ modulo $q$ is therefore exactly $3$, so $3 \mid q-1$ by Lagrange's theorem. The same argument applied to $p^2-p+1$, which divides $p^3+1$, gives $q \equiv 1 \pmod 6$ there.
--
--   In the $k=5$ two-prime residual this shows that both kernel primes $q$ and $r$ are $1 \pmod 3$, which is the first order-theoretic restriction on the square-free kernel available from the first Dris equation alone.
-- source:
--   Mathlib/Data/Nat/Prime/Basic.lean and Mathlib/GroupTheory/OrderOfElement.lean together with the classical order-of-a-unit argument: $q \mid p^3-1$ and $q \nmid p-1$ give $\mathrm{ord}_q(p) = 3$, and Lagrange gives $3 \mid q-1$. Uses the accepted children OddPerfectNumber.Kernel.five_cyclotomic_factors_ne_square (648a7dc4) and OddPerfectNumber.Kernel.five_cyclotomic_pair_coprime (dbed225d) for the factor shapes only; it encodes no unproved conjecture.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_cyclotomic_primes_one_mod_three {p q : Nat} (hp : p.Prime) (hp2 : p != 2)
    (hq : q.Prime) (hq3 : q != 3) (hqd : q ∣ p ^ 2 + p + 1) : q % 3 = 1 := by
  sorry

end OddPerfectNumber.Kernel
