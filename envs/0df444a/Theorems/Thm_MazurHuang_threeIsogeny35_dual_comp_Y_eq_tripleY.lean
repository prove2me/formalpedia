-- Prove2me | Theorems.Thm_MazurHuang_threeIsogeny35_dual_comp_Y_eq_tripleY
-- name    : MazurHuang.threeIsogeny35_dual_comp_Y_eq_tripleY
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:13.873232+00:00
-- url     : https://prove2.me/theorems/988d844d-5ca4-4700-9b8f-d948bbf12d0a
-- title:
--   Second coordinate of the composite of the two 3-isogenies of conductor 35 equals the tripling formula
-- statement:
--   Let $(x,y)$ be a rational point of $E : y^2 = x^3 + (4x+28)^2$ with $x \neq 0$, and let $\varphi$, $\hat\varphi$ be the explicit $3$-isogenies of the definition `MazurHuang_ThreeIsogeny35`. Then the second coordinate of $\hat\varphi(\varphi(x,y))$, computed by the rational formulas, equals the chord-and-tangent expression `shortTripleY x y` for the second coordinate of $3\cdot(x,y)$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135.lean (dual_three_comp_y and its inputs).

import Mathlib
import Definitions.Def_MazurHuang_ThreeIsogeny35

open MazurHuang.ThreeIsogeny35

theorem MazurHuang.threeIsogeny35_dual_comp_Y_eq_tripleY
    {x y : ℚ} (hx : x ≠ 0) (h : OnE35Short x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) = shortTripleY x y := by sorry
