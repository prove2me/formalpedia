-- Prove2me | Theorems.Thm_MazurHuang_threeIsogeny35_dual_comp_eq_three_nsmul
-- name    : MazurHuang.threeIsogeny35_dual_comp_eq_three_nsmul
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:14.62048+00:00
-- url     : https://prove2.me/theorems/1c35bb68-d8ca-40b0-b7ec-8735ea42f6df
-- title:
--   The composite of the two 3-isogenies of conductor 35 is multiplication by 3
-- statement:
--   For every rational point $P$ of $E : y^2 = x^3 + (4x+28)^2$ (including the point at infinity),
--   $$\hat\varphi(\varphi(P)) = 3P ,$$
--   where $\varphi : E(\mathbb{Q}) \to E'(\mathbb{Q})$ and $\hat\varphi : E'(\mathbb{Q}) \to E(\mathbb{Q})$ are the point maps `threeIsogenyPoint` and `dualThreeIsogenyPoint`.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135.lean (dual_comp_threeIsogenyPoint and its inputs).

import Mathlib
import Definitions.Def_MazurHuang_ThreeIsogeny35

open MazurHuang.ThreeIsogeny35

theorem MazurHuang.threeIsogeny35_dual_comp_eq_three_nsmul
    (P : E35ShortPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P := by sorry
