-- Prove2me | Theorems.Thm_MazurHuang_x0_seventeen_two_isogeny_model_points
-- name    : MazurHuang.x0_seventeen_two_isogeny_model_points
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-07T17:12:04.209672+00:00
-- url     : https://prove2.me/theorems/8bf21694-c5cc-4eec-bd61-cebadf8abb1e
-- title:
--   Rational points of $Y^2=X(X^2+30X+289)$, a model of $X_0(17)$
-- statement:
--   Every rational affine point $(X,Y)$ on the elliptic curve $$Y^2=X(X^2+30X+289)$$ has $X=0$ or $X=17$. Equivalently the rational points are $\infty$, $(0,0)$ and $(17,\pm136)$, a cyclic group of order $4$ (rank zero).
--
--   This curve is the two-isogeny-translated model of $X_0(17)$ (Cremona 17a1, $y^2+xy+y=x^3-x^2-x-14$). It is the arithmetic input to the exclusion of rational points of order $17$ in Xiang Huang's Lean development.
-- source:
--   Xiang Huang, FLT fork, commit 51bbb4f191ad0d3753b87123635c100a638ae580 (Apache-2.0), https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/X017RationalPoints.lean (theorem eq_zero_or_K_or_T_or_neg_T on the standard model Y²=X(X²+a17·X+b17), a17=30, b17=289 in X017Model.lean).

import Mathlib

open scoped WeierstrassCurve.Affine

theorem MazurHuang.x0_seventeen_two_isogeny_model_points (X Y : ℚ)
    (h : Y ^ 2 = X ^ 3 + 30 * X ^ 2 + 289 * X) : X = 0 ∨ X = 17 := by sorry
