-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_isSq_of_sq_mul_eq_sq
-- name    : OddPerfectNumber.Kernel.isSq_of_sq_mul_eq_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T12:55:20.268071+00:00
-- url     : https://prove2.me/theorems/74779081-0da5-48da-adb9-8a8d0571f2d1
-- title:
--   Cancelling an explicit square factor from a square
-- statement:
--   If $a^2 \cdot x = m^2$ with $a, x$ nonzero, then $x$ is a perfect square. This is the cancellation step used on the $k=5$ branch of the Odd Perfect Number Conjecture: the first Dris equation $2m^2 = \sigma(p^5) s$ together with $\sigma(p^5) = 2UV$ and $s = q a^2$ yields $m^2 = a^2 (qUV)$, so $qUV$ must be a square, which the coprime-nonsquares child refutes. The proof is exponent bookkeeping: $(m^2).\mathrm{factorization}\, p$ is even at every prime, the contribution of $a^2$ is even, so the contribution of $x$ is even.
-- source:
--   Mathlib/Data/Nat/Factorization/Core.lean (factorization_mul, factorization_pow) together with the accepted child OddPerfectNumber.Kernel.isSq_iff_even_factorization (theorem 28b00e2d-2e78-4683-8075-7135bec4a50b), which converts even exponents into an explicit square witness. No conjecture-specific content.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem isSq_of_sq_mul_eq_sq {a x m : Nat} (ha : a ≠ 0) (hx : x ≠ 0) (h : a ^ 2 * x = m ^ 2) :
    ∃ y, y ^ 2 = x := by
  sorry

end OddPerfectNumber.Kernel
