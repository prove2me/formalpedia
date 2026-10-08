-- Prove2me | Theorems.Thm_MazurHuang_N19_short_flex_factor_is_rational_cube
-- name    : MazurHuang.N19.short_flex_factor_is_rational_cube
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:14.995827+00:00
-- url     : https://prove2.me/theorems/ac811882-e2ec-4ad3-845d-3a9f61141e47
-- title:
--   The short-model flex factor is a rational cube
-- statement:
--   Every rational point on y² = x³ + (2x+4)² has y − (2x+4) equal to a rational cube. Primitive integral coordinates and coprime flex factors give the descent.
-- source:
--   Apache-2.0; fork 51bbb4f191ad0d3753b87123635c100a638ae580; FLT/Assumptions/MazurProof/XDelta19Descent.lean:48-228; FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean:138-250

import Mathlib

theorem MazurHuang.N19.short_flex_factor_is_rational_cube {x y : ℚ} (h : y ^ 2 = x ^ 3 + (2 * x + 4) ^ 2) : ∃ r : ℚ, y - (2 * x + 4) = r ^ 3 := by sorry
