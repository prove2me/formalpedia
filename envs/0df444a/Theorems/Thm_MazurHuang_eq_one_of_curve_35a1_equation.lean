-- Prove2me | Theorems.Thm_MazurHuang_eq_one_of_curve_35a1_equation
-- name    : MazurHuang.eq_one_of_curve_35a1_equation
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:03.751535+00:00
-- url     : https://prove2.me/theorems/9986ff2a-ab51-44dd-a3c3-10dc564dcf41
-- title:
--   The affine rational points of the elliptic curve 35a1 have first coordinate 1
-- statement:
--   If $w, z \in \mathbb{Q}$ satisfy $z^2 + z = w^3 + w^2 + 9w + 1$, then $w = 1$. (This is the elliptic curve with Cremona label 35a1; its group of rational points is $\{O, (1,3), (1,-4)\}$, cyclic of order $3$.)
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean (E35_three_torsion_x_zero, E35_affine_w_eq_one).

import Mathlib

theorem MazurHuang.eq_one_of_curve_35a1_equation
    {w z : ℚ}
    (h : z ^ 2 + z = w ^ 3 + w ^ 2 + 9 * w + 1) :
    w = 1 := by sorry
