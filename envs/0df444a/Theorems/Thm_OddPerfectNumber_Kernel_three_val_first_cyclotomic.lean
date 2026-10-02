-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_three_val_first_cyclotomic
-- name    : OddPerfectNumber.Kernel.three_val_first_cyclotomic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T01:11:04.110001+00:00
-- url     : https://prove2.me/theorems/9f50d0c0-f685-4798-b8c8-83681ba98b43
-- title:
--   The first cyclotomic block has exactly one factor of three when $p \equiv 1 \pmod 3$
-- statement:
--   If $p \ge 4$ and $p \equiv 1 \pmod 3$, then $3$ divides $p^2+p+1$ but $9$ does not.
--
--   Write $p = 3k+1$. Then $p^2+p+1 = 9k^2+9k+3 = 3(3k^2+3k+1)$, and the bracket is $1 \bmod 3$, so the block contains exactly one factor of $3$.
--
--   **Consequence for the $k=5$ two-prime residual.** The proved theorem `five_two_prime_cyclotomic_split` states that in the two-prime square-free-index case the first cyclotomic block is $q x^2$ or $r x^2$ for one of the two kernel primes $q, r$. A single factor of $3$ cannot be absorbed into the square, so $3$ must equal $q$ or $r$. Hence whenever $p \equiv 1 \pmod 3$, the prime $3$ is one of the two odd-multiplicity primes of the Dris index. This is a genuine square-class restriction coming from the FIRST Dris equation alone.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- When `p = 1 (mod 3)` the first cyclotomic block carries EXACTLY one factor of `3`.

Since `five_two_prime_cyclotomic_split` gives `p^2 + p + 1 = q * x^2` or `= r * x^2`,
the lone factor of `3` cannot be absorbed into the square `x^2`, so `3` is one of the two
kernel primes. -/
theorem three_val_first_cyclotomic {p : Nat} (hp4 : 4 <= p) (hp3 : p % 3 = 1) :
    (3 : Nat) ∣ p ^ 2 + p + 1 ∧ ¬ (9 : Nat) ∣ p ^ 2 + p + 1 := by
  sorry

end OddPerfectNumber.Kernel
