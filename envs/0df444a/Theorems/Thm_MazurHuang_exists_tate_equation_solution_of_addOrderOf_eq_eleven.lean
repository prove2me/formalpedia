-- Prove2me | Theorems.Thm_MazurHuang_exists_tate_equation_solution_of_addOrderOf_eq_eleven
-- name    : MazurHuang.exists_tate_equation_solution_of_addOrderOf_eq_eleven
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T14:13:54.490148+00:00
-- url     : https://prove2.me/theorems/ef5a6bc1-f584-4309-8907-d2586430bb11
-- title:
--   A rational point of order 11 gives a rational point with $b\neq 0$ on the order-11 Tate equation $F_{11}(b,c)=0$
-- statement:
--   Let $E$ be an elliptic curve over $\mathbb{Q}$ and suppose that $P \in E(\mathbb{Q})$ is a rational point of exact order $11$. Then there are rational numbers $b$ and $c$ with $b \neq 0$ such that
--
--   $$
--   \bigl(c^3 - b(b-c)\bigr)\,(b-c)^3 \;-\; b\,c\,\bigl(b-c-c^2\bigr)^3 \;=\; 0 .
--   $$
--
--   The polynomial on the left, $F_{11}(b,c)$, is the essential factor of the $11$-th division polynomial of the Tate normal form $E_{b,c} : y^2 + (1-c)xy - by = x^3 - bx^2$ at its marked point: $\psi_{11}(0,0) = b^{40}\,F_{11}(b,c)$. The equation $F_{11}(b,c)=0$ is therefore an affine plane model of the modular curve $X_1(11)$, and the theorem turns a rational point of order $11$ into a rational point of that model away from the locus $b=0$. Together with the determination of the rational points of $X_1(11)$ this excludes rational $11$-torsion.
--
--   **Formalization Note** "Exact order $11$" is `addOrderOf P = 11` in the group of rational points of $E$. The statement keeps only the two parameters and the equation; that $E_{b,c}$ is nonsingular and that $(0,0)$ has order $11$ on it are established in the proof but are not part of the conclusion.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0

import Mathlib

open scoped WeierstrassCurve.Affine

theorem MazurHuang.exists_tate_equation_solution_of_addOrderOf_eq_eleven
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P : (E⁄ℚ).Point) (hP : addOrderOf P = 11) :
    ∃ b c : ℚ, b ≠ 0 ∧
      (c ^ 3 - b * (b - c)) * (b - c) ^ 3 - b * c * (b - c - c ^ 2) ^ 3 = 0 := by sorry
