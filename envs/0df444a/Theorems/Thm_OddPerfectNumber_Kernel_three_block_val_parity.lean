-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_three_block_val_parity
-- name    : OddPerfectNumber.Kernel.three_block_val_parity
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-02T02:06:29.083425+00:00
-- url     : https://prove2.me/theorems/e9b72026-58b9-4365-93ab-24f940716b33
-- title:
--   The $3$-adic valuation of the cyclotomic product flips parity with $v_3(p+1)$
-- statement:
--   For $p \equiv 2 \pmod 3$, write $p = 3k+2$. Then $p^2-p+1 = 9k^2+9k+3$ carries exactly one factor of $3$, while $p+1 = 3(k+1)$ carries $v_3(p+1)$, and $3 \nmid p^2+p+1$. Hence
--
--   $$v_3\!\left(\tfrac{p+1}{2}\,(p^2+p+1)\,(p^2-p+1)\right) = v_3(p+1) + 1.$$
--
--   So the product has ODD $3$-adic valuation exactly when $v_3(p+1)$ is EVEN. Verified numerically for all $1052$ primes $p<40000$ with $p\equiv1\pmod4$ and $p\equiv2\pmod3$, with no counterexample.
--
--   **Consequence for the $k=5$ two-prime residual.** The first Dris equation reads $m^2 = (p^2+p+1)\cdot\tfrac{p+1}{2}(p^2-p+1)\cdot d_1^2 qr$, so the parity of that $3$-adic valuation must match the number of kernel primes equal to $3$. Together with `three_kernel_prime_when_p_one_mod_three` this makes the two cases complementary: every $p \equiv 1 \pmod 3$ forces $3$ into the kernel, and for $p \equiv 2 \pmod 3$ it does so exactly when $v_3(p+1)$ is even.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- The cyclotomic product carries an odd `3`-adic valuation exactly when `p + 1` does not. -/
theorem three_block_val_parity (p : Nat) (hp : p % 3 = 2) :
    Odd (((p + 1) / 2 * (p ^ 2 + p + 1) * (p ^ 2 - p + 1)).factorization 3) <-> (p + 1).factorization 3 % 2 = 0 := by
  sorry

end OddPerfectNumber.Kernel
