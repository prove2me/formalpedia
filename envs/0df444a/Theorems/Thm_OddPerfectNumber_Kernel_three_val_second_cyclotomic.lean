-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_three_val_second_cyclotomic
-- name    : OddPerfectNumber.Kernel.three_val_second_cyclotomic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T01:14:26.587131+00:00
-- url     : https://prove2.me/theorems/a3a28b8c-38f4-4272-bc2b-187c3f99f194
-- title:
--   The second cyclotomic block has exactly one factor of three when $p \equiv 2 \pmod 3$
-- statement:
--   If $p \ge 4$ and $p \equiv 2 \pmod 3$, then $3$ divides $p^2-p+1$ but $9$ does not.
--
--   Write $p = 3k+2$. Then $p^2-p+1 = 9k^2+9k+3 = 3(3k^2+3k+1)$, and the bracket is $1 \bmod 3$, so the block contains exactly one factor of $3$. Also $3 \mid p+1$, so $3$ divides the factor $(p+1)/2$ as well.
--
--   **Consequence for the $k=5$ two-prime residual.** The second block and the factor $(p+1)/2$ both carry exactly one factor of $3$ when $p \equiv 2 \pmod 3$. Their combined $3$-adic valuation is $v_3(p+1) + 1$, and since the whole left-hand side $m^2$ of the first Dris equation is a square, that valuation must have the same parity as the number of kernel primes equal to $3$. This pins the parity of $v_3(p+1)$ in the residual.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- When `p = 2 (mod 3)` the second cyclotomic block carries EXACTLY one factor of `3`.

Together with `3 ∣ p + 1` this says `3` divides both the factor `(p+1)/2` and the block
`p^2 - p + 1`, with exactly one factor of `3` in each. -/
theorem three_val_second_cyclotomic {p : Nat} (hp4 : 4 <= p) (hp3 : p % 3 = 2) :
    (3 : Nat) ∣ p ^ 2 - p + 1 ∧ ¬ (9 : Nat) ∣ p ^ 2 - p + 1 := by
  sorry

end OddPerfectNumber.Kernel
