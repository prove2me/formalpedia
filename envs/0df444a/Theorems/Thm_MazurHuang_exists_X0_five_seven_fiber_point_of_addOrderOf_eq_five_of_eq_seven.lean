-- Prove2me | Theorems.Thm_MazurHuang_exists_X0_five_seven_fiber_point_of_addOrderOf_eq_five_of_eq_seven
-- name    : MazurHuang.exists_X0_five_seven_fiber_point_of_addOrderOf_eq_five_of_eq_seven
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:10.581719+00:00
-- url     : https://prove2.me/theorems/c28677ae-dcc8-44e5-8def-1eb9f670f8dc
-- title:
--   Rational points of orders 5 and 7 on one elliptic curve give a rational point on the fibre product of X_0(5) and X_0(7)
-- statement:
--   Let $E$ be an elliptic curve over $\mathbb{Q}$ with rational points $P$ of exact order $5$ and $Q$ of exact order $7$. Then there are nonzero $a, b \in \mathbb{Q}$ with
--   $$b\,(a^2+10a+5)^3 = a\,(b^2+13b+49)(b^2+5b+1)^3 .$$
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/TateOriginDivision.lean, FLT/Assumptions/MazurProof/CyclicExclusion35.lean (simultaneous_orders_five_seven_to_X035_fiber and its inputs).

import Mathlib

open scoped WeierstrassCurve.Affine

theorem MazurHuang.exists_X0_five_seven_fiber_point_of_addOrderOf_eq_five_of_eq_seven
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P Q : (E⁄ℚ).Point)
    (hP : addOrderOf P = 5) (hQ : addOrderOf Q = 7) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧
      b * (a ^ 2 + 10 * a + 5) ^ 3 = a * ((b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3) := by sorry
