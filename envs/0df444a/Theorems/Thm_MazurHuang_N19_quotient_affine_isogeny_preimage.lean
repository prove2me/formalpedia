-- Prove2me | Theorems.Thm_MazurHuang_N19_quotient_affine_isogeny_preimage
-- name    : MazurHuang.N19.quotient_affine_isogeny_preimage
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:10.214097+00:00
-- url     : https://prove2.me/theorems/4a325715-fbb0-453f-b1e0-fcb0baf1100b
-- title:
--   Rational surjectivity of the good-model three-isogeny
-- statement:
--   Every rational affine point of t²=s³−3(24s+12)² has a rational preimage with nonzero horizontal coordinate under the explicit degree-three isogeny from y²=x³+(8x+76)².
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodDualDescent.lean:20-675; RationalPointsX135Descent.lean:3-136,569-576,656-858,874-911,1113-1173

import Mathlib

theorem MazurHuang.N19.quotient_affine_isogeny_preimage {s t : ℚ} (h : t ^ 2 = s ^ 3 - 3 * (24 * s + 12) ^ 2) :
    ∃ x y : ℚ, x ≠ 0 ∧ y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2 ∧
      (9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936) / x ^ 2 = s ∧
      (27 * x ^ 3 * y - 65664 * x * y - 1247616 * y) / x ^ 3 = t := by sorry
