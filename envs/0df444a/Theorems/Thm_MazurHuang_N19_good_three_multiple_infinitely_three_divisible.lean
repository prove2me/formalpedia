-- Prove2me | Theorems.Thm_MazurHuang_N19_good_three_multiple_infinitely_three_divisible
-- name    : MazurHuang.N19.good_three_multiple_infinitely_three_divisible
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:22.125015+00:00
-- url     : https://prove2.me/theorems/f98c2fb3-975c-43b6-a766-f43ee77ad80c
-- title:
--   Every triple is divisible by every power of three
-- statement:
--   For any rational point P on the good conductor-nineteen curve and any nonnegative integer n, there is a rational point Q with 3P=3ⁿ(3Q). This is the iterated consequence of the two complementary three-isogeny descents.
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodDescent.lean:373-471; XDelta19GoodDualDescent.lean:655-675; XDelta19GoodWeakDescent.lean:15-210; XDelta19GoodFormalCore.lean:543-565

import Mathlib

theorem MazurHuang.N19.good_three_multiple_infinitely_three_divisible (E : WeierstrassCurve ℚ) [E.IsElliptic] (hE : E = (⟨0, 64, 0, 1216, 5776⟩ : WeierstrassCurve ℚ))
    (P : WeierstrassCurve.Affine.Point E) (n : ℕ) :
    ∃ Q : WeierstrassCurve.Affine.Point E, 3 • P = (3 ^ n : ℕ) • (3 • Q) := by sorry
