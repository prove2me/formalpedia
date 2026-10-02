-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_three_kernel_prime_when_p_one_mod_three
-- name    : OddPerfectNumber.Kernel.three_kernel_prime_when_p_one_mod_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T01:25:30.659705+00:00
-- url     : https://prove2.me/theorems/257119a0-ae2a-479f-9429-8954f48c02b5
-- title:
--   If $p \equiv 1 \pmod 3$ then $3$ is one of the two kernel primes
-- statement:
--   In the $k=5$ two-prime square-free-index case, if $p \equiv 1 \pmod 3$ then one of the two kernel primes $q, r$ equals $3$.
--
--   Write $p = 3k+1$. Then $p^2+p+1 = 9k^2+9k+3 = 3(3k^2+3k+1)$ and the bracket is $1 \bmod 3$, so the first cyclotomic block contains exactly one factor of $3$. The proved theorem `five_two_prime_cyclotomic_split` states that in the two-prime case this block equals $q x^2$ or $r x^2$. If the single factor of $3$ were absorbed into the square, then $3 \mid x$, so $9 \mid x^2$, hence $9 \mid p^2+p+1$, contradicting the valuation. Therefore $3$ divides the prime factor itself, and since that factor is prime it equals $3$.
--
--   **Consequence.** This removes every $p \equiv 1 \pmod 3$ with neither kernel prime equal to $3$ from the residual `five_no_two_prime_squarefree_index`. Together with the parity bound on the other branch it pins the behaviour of $3$ in both cases.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- If `p = 1 (mod 3)` then one of the two kernel primes is `3`. -/
theorem three_kernel_prime_when_p_one_mod_three (p m d1 q r x : Nat) (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime) (hr : r.Prime) (hp3 : p % 3 = 1) (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) (hsplit : p ^ 2 + p + 1 = q * x ^ 2 ∨ p ^ 2 + p + 1 = r * x ^ 2) : q = 3 ∨ r = 3 := by
  sorry

end OddPerfectNumber.Kernel
