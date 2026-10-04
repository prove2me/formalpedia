-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_coprime_first_mod_three
-- name    : OddPerfectNumber.Kernel.five_cyclotomic_coprime_first_mod_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T07:47:41.08008+00:00
-- url     : https://prove2.me/theorems/9af6f99a-b577-4d37-8d0d-a4c975e28d6d
-- title:
--   The two $k=5$ cyclotomic blocks are coprime when $p \equiv 1 \pmod 3$
-- statement:
--   The two non-linear cyclotomic blocks that appear in the $k=5$ Dris equation are
--   $$C = p^2 + p + 1 \qquad\text{and}\qquad D = p^2 - p + 1,$$
--   together with the linear factor $(p+1)/2$. In the two-prime square-free-index case one has
--   $$m^2 = \frac{p+1}{2} \cdot C \cdot D \cdot d_1^2 \cdot q \cdot r,$$
--   so the odd-multiplicity prime support of every block must be contained in $\{q, r\}$.
--   The counting theorem used to make that inference, `two_prime_block_is_prime_mul_sq`, requires the two blocks to be **coprime**, and the first-block instance of that coprimality has already been proved: $\gcd\bigl(C, \tfrac{p+1}{2} D\bigr) = 1$ for every odd prime $p$.
--
--   The second-block instance is subtler. Writing $p = 3k+2$ gives
--   $$D = p^2 - p + 1 = 3\,(3k^2 + 3k + 1),$$
--   and the bracket is $1 \bmod 3$, so $v_3(D) = 1$; simultaneously $3 \mid p+1$, so
--   $3 \mid \tfrac{p+1}{2}$. Hence the factor $3$ is common to $D$ and to $\tfrac{p+1}{2} C$, and indeed one has
--   $3 \mid \gcd\bigl(\tfrac{p+1}{2} C,\, D\bigr)$ precisely when $p \equiv 2 \pmod 3$; numerically over all primes below $4000$ the gcd is $3$ for every $p \equiv 2 \pmod 3$ and $1$ otherwise. So the unconditional second-block coprimality is **false**, and the hypothesis $p \equiv 1 \pmod 3$ is exactly what removes the obstruction.
--
--   Under that hypothesis $3 \nmid p+1$, hence $3 \nmid \tfrac{p+1}{2}$ and $3 \nmid D$; and every other prime dividing both blocks is ruled out by the same short Euclidean argument that proves the first-block case.
--
--   **Consequence.** This supplies the coprimality hypothesis that the second-block split `five_two_prime_cyclotomic_split_second` (target 793eb5c3-69c0-425d-b3b1-7f4719cfa0f1) needs in the $p \equiv 1 \pmod 3$ case. In the $p \equiv 2 \pmod 3$ case the factor $3$ must instead be handled by valuation, using the children `three_val_second_cyclotomic` and `three_kernel_prime_when_p_two_mod_three`.
-- source:
--   Dris conjecture k=5 branch, Odd Perfect Number Conjecture mission. Complement of the proved target OddPerfectNumber.Kernel.five_cyclotomic_block_coprime (theorem_id 2c9214f0-5184-4b67-b5c8-b83681903eba), which states the first-block instance for every odd prime. Cyclotomic factorisation sigma(p^5) = (p+1)(p^2+p+1)(p^2-p+1).

import Mathlib

namespace OddPerfectNumber.Kernel

/-- If `p = 1 (mod 3)` then `(p^2 + p + 1)` and `((p + 1) / 2) * (p ^ 2 - p + 1)`
are coprime, and so are `(p ^ 2 - p + 1)` and `((p + 1) / 2) * (p ^ 2 + p + 1)`. -/
theorem five_cyclotomic_coprime_first_mod_three (p : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp3 : p % 3 = 1) :
    Nat.gcd (p ^ 2 + p + 1) (((p + 1) / 2) * (p ^ 2 - p + 1)) = 1 /\
    Nat.gcd (((p + 1) / 2) * (p ^ 2 + p + 1)) (p ^ 2 - p + 1) = 1 := by
  sorry

end OddPerfectNumber.Kernel
