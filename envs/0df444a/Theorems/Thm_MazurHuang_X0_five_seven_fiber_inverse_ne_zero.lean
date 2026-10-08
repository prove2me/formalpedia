-- Prove2me | Theorems.Thm_MazurHuang_X0_five_seven_fiber_inverse_ne_zero
-- name    : MazurHuang.X0_five_seven_fiber_inverse_ne_zero
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:05.793856+00:00
-- url     : https://prove2.me/theorems/b0a6750c-fca5-4ec8-aa00-d322ec6443f1
-- title:
--   Non-vanishing of the numerator and denominator of the inverse map on the fibre product of X_0(5) and X_0(7)
-- statement:
--   Let $a, b \in \mathbb{Q}$ satisfy
--   $$b\,(a^2+10a+5)^3 = a\,(b^2+13b+49)(b^2+5b+1)^3 .$$
--   Put
--   $$N = 3 - 74b - 63b^2 - 14b^3 - b^4 + 23a - 54ab - 63ab^2 - 14ab^3 - ab^4 + 4a^2 + 4a^2b,$$
--   $$D = 347b + 384b^2 + 133b^3 + 19b^4 + b^5 - 136a - 15ab + 4ab^2 - 51a^2 - 8a^2b + a^2b^2 - 4a^3 - a^3b .$$
--   Then $N \neq 0$, and if $b \neq 0$ then $D \neq 0$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135.lean (inverseXNum_ne_zero, inverseXDen_ne_zero and their inputs).

import Mathlib

theorem MazurHuang.X0_five_seven_fiber_inverse_ne_zero
    {a b : ℚ}
    (h : b * (a ^ 2 + 10 * a + 5) ^ 3 = a * ((b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3)) :
    3 - 74 * b - 63 * b ^ 2 - 14 * b ^ 3 - b ^ 4 + 23 * a - 54 * a * b -
        63 * a * b ^ 2 - 14 * a * b ^ 3 - a * b ^ 4 + 4 * a ^ 2 +
        4 * a ^ 2 * b ≠ 0 ∧
      (b ≠ 0 →
        347 * b + 384 * b ^ 2 + 133 * b ^ 3 + 19 * b ^ 4 + b ^ 5 - 136 * a -
        15 * a * b + 4 * a * b ^ 2 - 51 * a ^ 2 - 8 * a ^ 2 * b +
        a ^ 2 * b ^ 2 - 4 * a ^ 3 - a ^ 3 * b ≠ 0) := by sorry
