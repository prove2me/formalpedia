-- Prove2me | Theorems.Thm_MazurHuang_eq_zero_of_X0_thirtyFive_equation
-- name    : MazurHuang.eq_zero_of_X0_thirtyFive_equation
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:54.811433+00:00
-- url     : https://prove2.me/theorems/330252c3-7ab1-4646-9a54-abc87dcbf5fe
-- title:
--   Rational points of Kubert's hyperelliptic model of X_0(35) have x = 0
-- statement:
--   If $x, y \in \mathbb{Q}$ satisfy
--   $$y^2 = x^8 - 4x^7 - 6x^6 - 4x^5 - 9x^4 + 4x^3 - 6x^2 + 4x + 1 ,$$
--   then $x = 0$. The equation is Kubert's hyperelliptic model of the modular curve $X_0(35)$; its only affine rational points are $(0,\pm1)$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135.lean (map_to_E35, quotientW_ne_one). Mathematical source of the model: D. S. Kubert, Universal bounds on the torsion of elliptic curves, Proc. London Math. Soc. 33 (1976).

import Mathlib

theorem MazurHuang.eq_zero_of_X0_thirtyFive_equation
    {x y : ℚ}
    (h : y ^ 2 = x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 + 4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1) :
    x = 0 := by sorry
