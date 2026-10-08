-- Prove2me | Theorems.Thm_MazurHuang_N19_minimal_affine_x_eq_zero
-- name    : MazurHuang.N19.minimal_affine_x_eq_zero
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T14:55:22.036795+00:00
-- url     : https://prove2.me/theorems/fdc8b044-6ad9-422f-ae40-024e367c001c
-- title:
--   Rational points on the order-nineteen diamond quotient
-- statement:
--   Let $u,v\in\mathbb{Q}$ satisfy $v^2+v=u^3+u^2+u$. Then $u=0$. This is the affine rational-point classification of the minimal order-nineteen diamond quotient.
-- source:
--   https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580

import Mathlib

theorem MazurHuang.N19.minimal_affine_x_eq_zero {u v : ℚ} (h : v ^ 2 + v = u ^ 3 + u ^ 2 + u) : u = 0 := by sorry
