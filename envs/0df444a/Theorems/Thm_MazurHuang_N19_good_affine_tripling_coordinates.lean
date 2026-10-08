-- Prove2me | Theorems.Thm_MazurHuang_N19_good_affine_tripling_coordinates
-- name    : MazurHuang.N19.good_affine_tripling_coordinates
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:23.854454+00:00
-- url     : https://prove2.me/theorems/4eb76ad4-1662-41ba-8675-bdba9ea2ccb0
-- title:
--   Affine coordinates of multiplication by three on the good model
-- statement:
--   Away from x=0, tripling a nonsingular rational point on the good conductor-nineteen curve is the composition of the displayed forward and dual three-isogeny coordinate formulas.
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodIsogeny.lean:32-481

import Mathlib

theorem MazurHuang.N19.good_affine_tripling_coordinates (E : WeierstrassCurve ℚ) [E.IsElliptic] (hE : E = (⟨0, 64, 0, 1216, 5776⟩ : WeierstrassCurve ℚ)) {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E x y) (hx : x ≠ 0) :
    let s := (9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936) / x ^ 2
    let t := (27 * x ^ 3 * y - 65664 * x * y - 1247616 * y) / x ^ 3
    let u := (s ^ 3 - 2304 * s ^ 2 - 3456 * s - 1728) / (81 * s ^ 2)
    let v := (s ^ 3 * t + 3456 * s * t + 3456 * t) / (729 * s ^ 3)
    ∃ h' : WeierstrassCurve.Affine.Nonsingular E u v,
      3 • (WeierstrassCurve.Affine.Point.some x y h : WeierstrassCurve.Affine.Point E) = WeierstrassCurve.Affine.Point.some u v h' := by sorry
