-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_second_cyclotomic_product_not_square
-- name    : OddPerfectNumber.Kernel.five_second_cyclotomic_product_not_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T17:27:46.443386+00:00
-- url     : https://prove2.me/theorems/62a8c541-3d64-4dbc-b6e1-bf25ce65cdf7
-- title:
--   For prime p = 1 mod 4, ((p+1)/2)(p^2-p+1) is not a square
-- statement:
--   For a prime $p$ with $p \equiv 1 \pmod 4$, the product $V = \frac{p+1}{2}\,(p^2-p+1)$ is not a perfect square. Write $A = \frac{p+1}{2}$ and $B = p^2-p+1$, so $V = AB$. If a number $d$ divides both $A$ and $B$, then $d$ divides $p+1$ because $2A = p+1$, and then $d$ divides $B-(p-2)(p+1) = 3$; hence $\gcd(A,B)$ divides $3$, so it is $1$ or $3$. In the coprime case a square product forces each factor to be a square, contradicting the accepted fact that $p^2-p+1$ lies strictly between the consecutive squares $(p-1)^2$ and $p^2$. In the remaining case $\gcd(A,B)=3$, writing $A=3A'$, $B=3B'$ with $A',B'$ coprime forces $B'=z^2$, so $B=3z^2$. But $p\equiv1\pmod 4$ gives $B = p^2-p+1 \equiv 1 \pmod 4$, while $3z^2$ is $0$ or $3 \pmod 4$, a contradiction. The unconditional statement is false: at $p=23$ the product is $6084 = 78^2$, and $23\equiv3\pmod4$. The hypothesis $p\equiv1\pmod4$ is therefore essential and no deep Diophantine input is needed.
-- source:
--   Odd Perfect Number Conjecture, $k=5$ branch. In the first Dris equation $2m^2 = \sigma(p^5) s$ one has $\sigma(p^5) = 2UV$ with $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$, so a Dris index that is a single prime times a square would force $UV$ to be a square times that prime. The accepted child OddPerfectNumber.Kernel.five_cyclotomic_factors_ne_square (648a7dc4-9710-4052-8b9c-50b2d545ffbb) already supplies that $p^2-p+1$ is not a square for $2<p$, so only the product needs an argument. The unconditional statement is false, since $p=23$ gives $V=6084=78^2$; the hypothesis $p\equiv1\pmod4$ excludes exactly that case through the congruence $p^2-p+1\equiv1\pmod4$ versus $3z^2\in\{0,3\}\pmod4$, so no deep Diophantine input is required.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_second_cyclotomic_product_not_square (p : Nat) (hp : p.Prime) (hp4 : p % 4 = 1) :
    ¬ ∃ y : Nat, ((p + 1) / 2) * (p ^ 2 - p + 1) = y ^ 2 := by
  sorry

end OddPerfectNumber.Kernel
