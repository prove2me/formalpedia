-- Prove2me | Theorems.Thm_MazurHuang_eq_zero_or_eq_neg_four_of_X1_eleven_equation
-- name    : MazurHuang.eq_zero_or_eq_neg_four_of_X1_eleven_equation
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T14:14:05.553805+00:00
-- url     : https://prove2.me/theorems/6de2ccc1-9c95-45a7-b791-9ae2ca614993
-- title:
--   Rational points of $X_1(11)$: $Y^2 = X^3+8X^2+16X+16$ has only the rational points with $X\in\{0,-4\}$
-- statement:
--   Let $X$ and $Y$ be rational numbers with
--
--   $$
--   Y^2 = X^3 + 8X^2 + 16X + 16 .
--   $$
--
--   Then $X = 0$ or $X = -4$. Equivalently, the only rational affine points of this cubic are $(0,\pm 4)$ and $(-4,\pm 4)$.
--
--   The cubic is an elliptic curve of conductor $11$: the substitution $X = 4x - 4$, $Y = 8y + 4$ identifies it with $y^2 + y = x^3 - x^2$ (Cremona label 11a3), a model of the modular curve $X_1(11)$. The theorem says that its Mordell–Weil group over $\mathbb{Q}$ consists of the point at infinity and the four listed points, so it is cyclic of order $5$ and has rank $0$; all five rational points are cusps of $X_1(11)$. This is the arithmetic input that excludes rational points of order $11$ on elliptic curves over $\mathbb{Q}$, and it is a classical theorem of Billing and Mahler (1940).
--
--   **Formalization Note** The statement is purely about rational numbers; no elliptic-curve structure appears in it. The proof is a complete $2$-descent carried out in the cubic field $\mathbb{Q}(\alpha)$, $\alpha^3-4\alpha^2+4\alpha-2=0$, which is defined inside the proof and not needed to state the result.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0

import Mathlib

theorem MazurHuang.eq_zero_or_eq_neg_four_of_X1_eleven_equation
    {X Y : ℚ} (h : Y ^ 2 = X ^ 3 + 8 * X ^ 2 + 16 * X + 16) : X = 0 ∨ X = -4 := by sorry
