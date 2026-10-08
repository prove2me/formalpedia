-- Prove2me | Theorems.Thm_MazurHuang_N19_good_dual_forward_vertical_coordinate
-- name    : MazurHuang.N19.good_dual_forward_vertical_coordinate
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:49.422418+00:00
-- url     : https://prove2.me/theorems/f2c1d152-ff68-48c1-bc2b-2917c6d571c3
-- title:
--   The vertical isogeny composition equals the tangent-chord tripling formula
-- statement:
--   On y²=x³+(8x+76)² with x nonzero, the vertical coordinate obtained by the forward and dual three-isogeny formulas equals the vertical coordinate obtained by tangent doubling followed by chord addition. All coordinates are given explicitly as rational expressions.
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodIsogeny.lean:31-170,209-277,331-362,393-429

import Mathlib

theorem MazurHuang.N19.good_dual_forward_vertical_coordinate {x y : ℚ} (hx : x ≠ 0)
    (h : y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2) :
    let tangent := (3 * x ^ 2 + 128 * x + 1216) / (2 * y)
    let doubleX := tangent ^ 2 - 64 - 2 * x
    let doubleY := -(tangent * (doubleX - x) + y)
    let tripleSlope := (doubleY - y) / (doubleX - x)
    let tripleX := tripleSlope ^ 2 - 64 - doubleX - x
    let s := (9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936) / x ^ 2
    let t := (27 * x ^ 3 * y - 65664 * x * y - 1247616 * y) / x ^ 3
    (s ^ 3 * t + 3456 * s * t + 3456 * t) / (729 * s ^ 3) =
      -(tripleSlope * (tripleX - doubleX) + doubleY) := by sorry
