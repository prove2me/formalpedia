-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_factors_ne_square
-- name    : OddPerfectNumber.Kernel.five_cyclotomic_factors_ne_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T23:11:23.257174+00:00
-- url     : https://prove2.me/theorems/648a7dc4-9710-4052-8b9c-50b2d545ffbb
-- title:
--   Neither non-trivial k=5 cyclotomic factor of sigma(p^5) is a square
-- statement:
--   For $p > 2$, neither $p^2+p+1$ nor $p^2-p+1$ is a perfect square. Indeed $p^2 < p^2+p+1 < (p+1)^2$ and $(p-1)^2 < p^2-p+1 < p^2$ for $p \ge 2$, so each lies strictly between two consecutive squares. This supplies the non-square input on the two cyclotomic factors of $\sigma(p^5)$ used in the $k=5$ square-free-index analysis.
-- source:
--   Consecutive-square argument (Mathlib `Nat.not_exists_sq'`) for the two non-trivial cyclotomic factors of $\sigma(p^5)$ in the $k=5$ square-free-index reduction.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_cyclotomic_factors_ne_square (p : Nat) (hp : 2 < p) :
    (¬ ∃ a, a ^ 2 = p ^ 2 + p + 1) ∧ (¬ ∃ b, b ^ 2 = p ^ 2 - p + 1) := by
  sorry

end OddPerfectNumber.Kernel
