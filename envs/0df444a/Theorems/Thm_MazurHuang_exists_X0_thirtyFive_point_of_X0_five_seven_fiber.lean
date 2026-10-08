-- Prove2me | Theorems.Thm_MazurHuang_exists_X0_thirtyFive_point_of_X0_five_seven_fiber
-- name    : MazurHuang.exists_X0_thirtyFive_point_of_X0_five_seven_fiber
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:11.94075+00:00
-- url     : https://prove2.me/theorems/310d702c-76c8-4b28-a94f-e35e56e7960d
-- title:
--   A non-cuspidal rational point of the fibre product of X_0(5) and X_0(7) gives a rational point of X_0(35) with x nonzero
-- statement:
--   Let $a, b \in \mathbb{Q}$ with $b \neq 0$ satisfy
--   $$b\,(a^2+10a+5)^3 = a\,(b^2+13b+49)(b^2+5b+1)^3 .$$
--   Then there are $x, y \in \mathbb{Q}$ with $x \neq 0$ and
--   $$y^2 = x^8 - 4x^7 - 6x^6 - 4x^5 - 9x^4 + 4x^3 - 6x^2 + 4x + 1 .$$
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135.lean (fiber_to_X035 and its inputs; the proof of the private lemma inverse_residual_zero is replaced by a kernel-checked coefficient-table computation).

import Mathlib

theorem MazurHuang.exists_X0_thirtyFive_point_of_X0_five_seven_fiber
    {a b : ℚ} (hb : b ≠ 0)
    (h : b * (a ^ 2 + 10 * a + 5) ^ 3 = a * ((b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3)) :
    ∃ x y : ℚ, x ≠ 0 ∧
      y ^ 2 = x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 + 4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1 := by sorry
