-- Prove2me | Theorems.Thm_MazurHuang_tate_origin_addOrderOf_ne_nineteen
-- name    : MazurHuang.tate_origin_addOrderOf_ne_nineteen
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-07T17:12:04.946904+00:00
-- url     : https://prove2.me/theorems/895925fb-1401-4edf-b71a-3d56251c2101
-- title:
--   No Tate normal form has a marked point of order $19$
-- statement:
--   Let $b,c\in\mathbb Q$ with $b\neq0$ and let $E_{b,c}: y^2+(1-c)xy-by=x^3-bx^2$ be the Tate normal form, assumed elliptic. Then the marked point $(0,0)\in E_{b,c}(\mathbb Q)$ does not have order $19$.
--
--   Together with the reduction of any rational point of order $>3$ to Tate normal form (MazurHuang.exists_tate_normal_form_of_addOrderOf_gt_three), this excludes rational points of order $19$ on every elliptic curve over $\mathbb Q$. The proof evaluates the division polynomial $\psi_{19}$ at the origin, factors out the order-19 Tate division equation $F_{19}(b,c)=0$, and maps a solution with $b\ne0$ to a point with $u\neq0$ on the quotient curve $v^2+v=u^3+u^2+u$.
-- source:
--   Xiang Huang, FLT fork, commit 51bbb4f191ad0d3753b87123635c100a638ae580 (Apache-2.0), https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/TateOrder19.lean (F19_eq_zero_of_tateOrigin_order_nineteen), TateOrder19Quotient.lean, N19SutherlandModels.lean.

import Mathlib

open scoped WeierstrassCurve.Affine

theorem MazurHuang.tate_origin_addOrderOf_ne_nineteen (b c : ℚ) (hb : b ≠ 0)
    [({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).IsElliptic]
    (h : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0) :
    addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) ≠ 19 := by sorry
