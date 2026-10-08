-- Prove2me | Theorems.Thm_MazurHuang_tate_origin_addOrderOf_ne_seventeen
-- name    : MazurHuang.tate_origin_addOrderOf_ne_seventeen
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-07T17:12:08.258986+00:00
-- url     : https://prove2.me/theorems/3ef44edf-cc7c-421c-b356-758ec32d8cd4
-- title:
--   No Tate normal form has a marked point of order $17$
-- statement:
--   Let $b,c\in\mathbb Q$ with $b\neq0$ and let $E_{b,c}: y^2+(1-c)xy-by=x^3-bx^2$ be the Tate normal form, assumed elliptic. Then the marked point $(0,0)\in E_{b,c}(\mathbb Q)$ does not have order $17$.
--
--   Together with the reduction to Tate normal form this excludes rational points of order $17$. The proof evaluates $\psi_{17}$ at the origin to get the order-17 Tate division equation $F_{17}(b,c)=0$, maps a solution with $b\ne0$ through two explicit two-isogenies to the model $Y^2=X(X^2+30X+289)$ of $X_0(17)$, and excludes the two possible fibres over its rational points by a quartic with no root modulo $3$ and the irrationality of $\sqrt{17}$.
-- source:
--   Xiang Huang, FLT fork, commit 51bbb4f191ad0d3753b87123635c100a638ae580 (Apache-2.0), https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/TateOrder17.lean (F17_eq_zero_of_tateOrigin_order_seventeen), TateOrder17Quotient.lean (no_F17_rational_solution).

import Mathlib

open scoped WeierstrassCurve.Affine

theorem MazurHuang.tate_origin_addOrderOf_ne_seventeen (b c : ℚ) (hb : b ≠ 0)
    [({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).IsElliptic]
    (h : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0) :
    addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) ≠ 17 := by sorry
