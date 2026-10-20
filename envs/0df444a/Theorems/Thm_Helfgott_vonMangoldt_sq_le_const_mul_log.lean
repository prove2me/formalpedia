-- Prove2me | Theorems.Thm_Helfgott_vonMangoldt_sq_le_const_mul_log
-- name    : Helfgott.vonMangoldt_sq_le_const_mul_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T19:02:34.835596+00:00
-- url     : https://prove2.me/theorems/c6442a29-0b15-49cb-bcd9-5272b283e796
-- title:
--   $\sum_{n\le X}\Lambda(n)^2 \le (\log 4+4)\,X\log X$
-- statement:
--   For every natural number $X \\ge 2$,
--
--   $$\\sum_{n \\le X} \\Lambda(n)^2 \\;\\le\\; (\\log 4 + 4)\\,X\\log X .$$
--
--   This is the immediately usable form of the $\\Lambda^2$ estimate: `$\\log X \\setminus$` times the explicitly bounded Chebyshev function, replacing $\\psi(X)$ by the library's absolute upper bound $\\psi(x) \\le (\\log 4 + 4)\\,x$ (valid for every $x \\ge 0$). In the minor-arc analysis this is the concrete constant that enters the Parseval block of the Helfgott minor-arc estimate: squared prime coefficients are summed in exactly this shape, and the inequality is what replaces any appeal to stronger-than-needed prime-number-theorem content.
--
--   **Formalization Note.** Real-valued on both sides; `2 \\le X` needed only to have `$\\log X$` nonnegative. Direct corollary of `Helfgott.vonMangoldt_sq_le_log_mul_psi` and `Chebyshev.psi_le_const_mul_self`.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes; L^2 Parseval block of the Helfgott minor-arc estimate; Chebyshev bound as in Mathlib's Chebyshev.psi_le_const_mul_self.

import Mathlib

namespace Helfgott

theorem vonMangoldt_sq_le_const_mul_log (X : ℕ) (hX : 2 ≤ X) :
    ∑ n ∈ Finset.Icc 0 X, (ArithmeticFunction.vonMangoldt n) ^ 2 ≤
      (Real.log 4 + 4) * (X : ℝ) * Real.log X := by sorry

end Helfgott
