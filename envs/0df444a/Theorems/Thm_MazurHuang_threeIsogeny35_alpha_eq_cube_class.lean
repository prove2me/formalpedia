-- Prove2me | Theorems.Thm_MazurHuang_threeIsogeny35_alpha_eq_cube_class
-- name    : MazurHuang.threeIsogeny35_alpha_eq_cube_class
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:05:58.883878+00:00
-- url     : https://prove2.me/theorems/6eca7688-2b89-4739-b2dc-42d0a60ae338
-- title:
--   On y^2 = x^3 + (4x+28)^2 the function y - (4x+28) is a rational cube times 1, 7 or 49
-- statement:
--   Let $x, y \in \mathbb{Q}$ satisfy $y^2 = x^3 + 16x^2 + 224x + 784$ (equivalently $y^2 = x^3 + (4x+28)^2$). Then there is $r \in \mathbb{Q}$ such that $y - (4x+28)$ equals $r^3$, $7r^3$ or $49r^3$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean (short_alpha_cubeclass and its inputs).

import Mathlib

theorem MazurHuang.threeIsogeny35_alpha_eq_cube_class
    {x y : ℚ}
    (h : y ^ 2 = x ^ 3 + 16 * x ^ 2 + 224 * x + 784) :
    ∃ r : ℚ,
      y - (4 * x + 28) = r ^ 3 ∨
      y - (4 * x + 28) = 7 * r ^ 3 ∨
      y - (4 * x + 28) = 49 * r ^ 3 := by sorry
