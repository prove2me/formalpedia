-- Prove2me | Theorems.Thm_MazurHuang_three_dvd_of_threeIsogeny35_cover_eq_zero
-- name    : MazurHuang.three_dvd_of_threeIsogeny35_cover_eq_zero
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:06.350918+00:00
-- url     : https://prove2.me/theorems/f44ad6d5-33f0-45b6-a3c8-339cdd0ae90d
-- title:
--   The cubic form X^3 - 3Y^3 + 3000Z^3 + 3X^2Y - 9XY^2 + 24X^2Z + 72Y^2Z vanishes only at integers divisible by 3
-- statement:
--   Let $X, Y, Z$ be integers with
--   $$X^3 - 3Y^3 + 3000Z^3 + 3X^2Y - 9XY^2 + 24X^2Z + 72Y^2Z = 0 .$$
--   Then $3 \mid X$, $3 \mid Y$ and $3 \mid Z$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean (statement of n35CoverRho_all_three_dvd; the proof here is a shorter one written for this submission).

import Mathlib

theorem MazurHuang.three_dvd_of_threeIsogeny35_cover_eq_zero
    {X Y Z : ℤ}
    (h : X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y -
      9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z = 0) :
    3 ∣ X ∧ 3 ∣ Y ∧ 3 ∣ Z := by sorry
