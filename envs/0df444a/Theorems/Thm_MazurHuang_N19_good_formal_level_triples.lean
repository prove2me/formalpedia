-- Prove2me | Theorems.Thm_MazurHuang_N19_good_formal_level_triples
-- name    : MazurHuang.N19.good_formal_level_triples
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:13.09098+00:00
-- url     : https://prove2.me/theorems/03084ba5-7bbf-426a-81dd-8443f3c2a6a3
-- title:
--   Tripling raises the exact three-adic formal level
-- statement:
--   A nonzero rational formal point with coordinate valuations v₃(x)=−2k and v₃(y)=−3k, k>0, remains nonzero after tripling and has exact level k+1.
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodFormalCore.lean:27-459

import Mathlib

theorem MazurHuang.N19.good_formal_level_triples (E : WeierstrassCurve ℚ) [E.IsElliptic] (hE : E = (⟨0, 64, 0, 1216, 5776⟩ : WeierstrassCurve ℚ))
    (P : WeierstrassCurve.Affine.Point E) (k : ℤ)
    (hP : (∃ (x y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular E x y), P = WeierstrassCurve.Affine.Point.some x y h ∧ 0 < k ∧ padicValRat 3 x = -2 * k ∧ padicValRat 3 y = -3 * k)) :
    (∃ (x y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular E x y), (3 • P) = WeierstrassCurve.Affine.Point.some x y h ∧ 0 < (k + 1) ∧ padicValRat 3 x = -2 * (k + 1) ∧ padicValRat 3 y = -3 * (k + 1)) := by sorry
