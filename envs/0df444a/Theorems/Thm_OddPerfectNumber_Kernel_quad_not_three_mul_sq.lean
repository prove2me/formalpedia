-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_quad_not_three_mul_sq
-- name    : OddPerfectNumber.Kernel.quad_not_three_mul_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T18:03:06.444669+00:00
-- url     : https://prove2.me/theorems/47b149df-afb7-4c73-aa82-c76a2033cf70
-- title:
--   For p = 1 mod 4, p^2 - p + 1 is never three times a square
-- statement:
--   If $p \equiv 1 \pmod 4$ then $p^2 - p + 1 \equiv 1 \pmod 4$, while $3z^2$ is $0$ or $3 \pmod 4$ for every $z$, so $p^2 - p + 1 \neq 3z^2$. This kills the $\gcd = 3$ branch of the proof that $V = \frac{p+1}{2}(p^2-p+1)$ is never a square for a prime $p \equiv 1 \pmod 4$.
-- source:
--   Odd Perfect Number Conjecture, $k=5$ branch. In the first Dris equation $2m^2 = \sigma(p^5) s$ one has $\sigma(p^5) = 2UV$ with $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$, so a Dris index that is a single prime times a square would force $UV$ to be a square times that prime. The accepted child OddPerfectNumber.Kernel.five_cyclotomic_factors_ne_square (648a7dc4-9710-4052-8b9c-50b2d545ffbb) already supplies that $p^2-p+1$ is not a square for $2<p$, so only the product needs an argument. The unconditional statement is false, since $p=23$ gives $V=6084=78^2$; the hypothesis $p\equiv1\pmod4$ excludes exactly that case through the congruence $p^2-p+1\equiv1\pmod4$ versus $3z^2\in\{0,3\}\pmod4$, so no deep Diophantine input is required.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem quad_not_three_mul_sq (p : Nat) (hp4 : p % 4 = 1) :
    ¬ ∃ z : Nat, (p ^ 2 - p + 1) = (3 * z ^ 2) := by
  sorry

end OddPerfectNumber.Kernel
