-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_second_block_gcd_dvd_three
-- name    : OddPerfectNumber.Kernel.second_block_gcd_dvd_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T18:08:30.930249+00:00
-- url     : https://prove2.me/theorems/0e45b51d-915a-4c31-bec6-b2f945374870
-- title:
--   A common divisor of (p+1)/2 and p^2-p+1 divides 3
-- statement:
--   If $p \equiv 1 \pmod 4$ then any common divisor of $A=\frac{p+1}{2}$ and $B=p^2-p+1$ divides $2A = p+1$ and hence $B - (p-2)(p+1) = 3$. Thus $\gcd(A,B)$ is $1$ or $3$, the two-case split needed to show $V = \frac{p+1}{2}(p^2-p+1)$ is never a square for a prime $p \equiv 1 \pmod 4$.
-- source:
--   Odd Perfect Number Conjecture, $k=5$ branch. In the first Dris equation $2m^2 = \sigma(p^5) s$ one has $\sigma(p^5) = 2UV$ with $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$, so a Dris index that is a single prime times a square would force $UV$ to be a square times that prime. The accepted child OddPerfectNumber.Kernel.five_cyclotomic_factors_ne_square (648a7dc4-9710-4052-8b9c-50b2d545ffbb) already supplies that $p^2-p+1$ is not a square for $2<p$, so only the product needs an argument. The unconditional statement is false, since $p=23$ gives $V=6084=78^2$; the hypothesis $p\equiv1\pmod4$ excludes exactly that case through the congruence $p^2-p+1\equiv1\pmod4$ versus $3z^2\in\{0,3\}\pmod4$, so no deep Diophantine input is required.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem second_block_gcd_dvd_three (p : Nat) (hp4 : p % 4 = 1) :
    Nat.gcd ((p + 1) / 2) (p ^ 2 - p + 1) ∣ 3 := by
  sorry

end OddPerfectNumber.Kernel
