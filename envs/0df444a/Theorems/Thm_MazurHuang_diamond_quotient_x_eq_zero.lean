-- Prove2me | Theorems.Thm_MazurHuang_diamond_quotient_x_eq_zero
-- name    : MazurHuang.diamond_quotient_x_eq_zero
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-07T17:12:03.021647+00:00
-- url     : https://prove2.me/theorems/161f512a-7fb5-4b32-86ac-5d047aa508e7
-- title:
--   Rational points of $v^2+v=u^3+u^2+u$ (the order-three diamond quotient of $X_1(19)$)
-- statement:
--   Every rational affine point $(u,v)$ on the elliptic curve $$v^2+v=u^3+u^2+u$$ has $u=0$; equivalently its only rational points are $\infty$, $(0,0)$ and $(0,-1)$, so the Mordell–Weil group is $\mathbb Z/3\mathbb Z$ (rank zero).
--
--   This curve is the quotient of $X_1(19)$ by the order-three subgroup of diamond operators. In Xiang Huang's Lean development it is the only arithmetic input to the exclusion of rational points of order $19$: an explicit algebraic map sends a nondegenerate solution of the order-19 Tate division equation to an affine point with $u\neq 0$.
-- source:
--   Xiang Huang, FLT fork, commit 51bbb4f191ad0d3753b87123635c100a638ae580 (Apache-2.0), https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/XDelta19RationalPoints.lean (theorem diamond_x_eq_zero); the rank-zero descent is in XDelta19Descent.lean and XDelta19Good*.lean. Mathematical background: Mazur, Modular curves and the Eisenstein ideal (1977); Ogg (1973).

import Mathlib

open scoped WeierstrassCurve.Affine

theorem MazurHuang.diamond_quotient_x_eq_zero (u v : ℚ)
    (h : v ^ 2 + v = u ^ 3 + u ^ 2 + u) : u = 0 := by sorry
