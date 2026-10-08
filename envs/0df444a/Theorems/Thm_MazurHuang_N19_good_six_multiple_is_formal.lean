-- Prove2me | Theorems.Thm_MazurHuang_N19_good_six_multiple_is_formal
-- name    : MazurHuang.N19.good_six_multiple_is_formal
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:13.28599+00:00
-- url     : https://prove2.me/theorems/184134ed-903b-4215-926c-bd82bc4a174f
-- title:
--   Six times every rational good-model point lies in the formal kernel
-- statement:
--   Six times every rational point on the good conductor-nineteen model is infinity or has coordinate valuations v₃(x)=−2k and v₃(y)=−3k for some positive integer k.
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodFormalReduction.lean:18-1172; XDelta19GoodFormalCore.lean:27-208,376-405,461-469

import Mathlib

theorem MazurHuang.N19.good_six_multiple_is_formal (E : WeierstrassCurve ℚ) [E.IsElliptic] (hE : E = (⟨0, 64, 0, 1216, 5776⟩ : WeierstrassCurve ℚ))
    (P : WeierstrassCurve.Affine.Point E) :
    ((6 • P) = 0 ∨ ∃ (x y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular E x y), (6 • P) = WeierstrassCurve.Affine.Point.some x y h ∧ ∃ k : ℤ, 0 < k ∧ padicValRat 3 x = -2 * k ∧ padicValRat 3 y = -3 * k) := by sorry
