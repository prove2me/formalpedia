-- Prove2me | Theorems.Thm_LefebvreVariations_tunnell_even_count_implies_curve_point_le_100
-- name    : LefebvreVariations.tunnell_even_count_implies_curve_point_le_100
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:21:42.71923+00:00
-- url     : https://prove2.me/theorems/bcf32064-36bf-40cc-bfc8-41f8477438e1
-- title:
--   Lefebvre's variations, No. 18 — on a theme by Tunnell: Tunnell's converse in the even case for $n\le 100$
-- statement:
--   This is the converse of Tunnell's criterion, in the even case, for all $n\le100$.
--
--   Let $n\le100$ be an even squarefree positive integer and put
--
--   $$
--   A(n)=\#\{(x,y,z)\in\mathbb Z^3:\ n=8x^2+2y^2+64z^2\},\qquad B(n)=\#\{(x,y,z)\in\mathbb Z^3:\ n=8x^2+2y^2+16z^2\}.
--   $$
--
--   If $2A(n)=B(n)$, then the elliptic curve $y^2=x^3-n^2x$ has a rational point with $y\neq0$, so $n$ is a congruent number.
--
--   Tunnell proved that every congruent $n$ satisfies $2A(n)=B(n)$, and that the converse follows from the Birch–Swinnerton-Dyer conjecture; the converse is open in general. Here it is established unconditionally in the range $n\le100$: the identity holds for exactly $n\in\{6,14,22,30,34,38,46,62,70,78,86,94\}$, and for each of these an explicit rational point is given, coming from a rational right triangle of area $n$ (for example the $(3,4,5)$ triangle for $n=6$).
--
--   **Formalization Note** The counts are `Set.ncard` of integer solution sets, as in the parent statement; for the other even squarefree $n\le100$ the identity fails and the implication holds vacuously.
--
--   **Why this is a variation.** This varies the open converse of Tunnell's theorem on congruent numbers (`Tunnell.even_count_implies_curve_point`): if the counting identity holds for an even squarefree $n$, then $y^2=x^3-n^2x$ has a nonzero rational point. Tunnell proved the converse only conditionally on the Birch–Swinnerton-Dyer conjecture; this is the unconditional partial result for all even squarefree $n\le 100$. It checks the converse on the first range of the congruent number problem, where the identity holds for exactly twelve values, each with an explicit rational point.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. B. Tunnell, A classical Diophantine problem and modular forms of weight 3/2, Invent. Math. 72 (1983), 323–334 (Theorem: if n is congruent then the counting identity holds; the converse follows from the Birch–Swinnerton-Dyer conjecture); N. Koblitz, Introduction to Elliptic Curves and Modular Forms, 2nd ed., Springer GTM 97, 1993, Chapter I and Chapter IV §4 (congruent numbers and the curve y² = x³ − n²x). Parent problem: Tunnell.even_count_implies_curve_point.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Tunnell's even-case count identity implies a nonzero rational point on `y² = x³ - n²x`,
for every squarefree even `n ≤ 100` (finite verification; the identity holds exactly for
`n ∈ {6, 14, 22, 30, 34, 38, 46, 62, 70, 78, 86, 94}`, all congruent numbers; Tunnell 1983). -/
theorem tunnell_even_count_implies_curve_point_le_100 (n : ℕ) (hn : n ≤ 100)
    (hsqf : Squarefree n) (hparity : Even n) :
    2 * ({(x, y, z) : ℤ × ℤ × ℤ | (n : ℤ) = 8 * x ^ 2 + 2 * y ^ 2 + 64 * z ^ 2} :
        Set (ℤ × ℤ × ℤ)).ncard =
      ({(x, y, z) : ℤ × ℤ × ℤ | (n : ℤ) = 8 * x ^ 2 + 2 * y ^ 2 + 16 * z ^ 2} :
        Set (ℤ × ℤ × ℤ)).ncard →
    ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := by
  sorry

end LefebvreVariations
