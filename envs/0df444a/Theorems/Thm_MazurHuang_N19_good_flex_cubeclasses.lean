-- Prove2me | Theorems.Thm_MazurHuang_N19_good_flex_cubeclasses
-- name    : MazurHuang.N19.good_flex_cubeclasses
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:06.63398+00:00
-- url     : https://prove2.me/theorems/081b92b0-d9e6-4777-a4e3-8fde401b5519
-- title:
--   Cubeclasses of the rational good-model flex function
-- statement:
--   For a rational point on y²=x³+(8x+76)², the flex value y−8x−76 is a cube, nineteen times a cube, or 361 times a cube.
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodDescent.lean:27-369

import Mathlib

theorem MazurHuang.N19.good_flex_cubeclasses {x y : ℚ} (h : y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2) :
    ∃ r : ℚ, y - (8 * x + 76) = r ^ 3 ∨ y - (8 * x + 76) = 19 * r ^ 3 ∨ y - (8 * x + 76) = 361 * r ^ 3 := by sorry
