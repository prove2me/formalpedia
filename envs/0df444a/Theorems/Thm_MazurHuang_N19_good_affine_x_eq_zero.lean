-- Prove2me | Theorems.Thm_MazurHuang_N19_good_affine_x_eq_zero
-- name    : MazurHuang.N19.good_affine_x_eq_zero
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T14:55:21.210029+00:00
-- url     : https://prove2.me/theorems/ba88051c-bd6b-42a9-a99d-a04f898eef42
-- title:
--   Rational points on the good conductor-nineteen model
-- statement:
--   Let $x,y\in\mathbb{Q}$ satisfy $y^2=x^3+(8x+76)^2$. Then $x=0$. This classifies the horizontal coordinate of every affine rational point on the good integral conductor-nineteen model.
-- source:
--   https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580

import Mathlib

theorem MazurHuang.N19.good_affine_x_eq_zero {x y : ℚ} (h : y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2) : x = 0 := by sorry
