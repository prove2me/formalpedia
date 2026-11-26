-- Prove2me | Theorems.Thm_LefebvreVariations_tunnell_odd_count_implies_curve_point_le_100
-- name    : LefebvreVariations.tunnell_odd_count_implies_curve_point_le_100
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:35:52.626067+00:00
-- url     : https://prove2.me/theorems/b4e604b1-4510-48bf-87cc-a56a58bb041a
-- title:
--   Lefebvre's variations, No. 16 — on a theme by Tunnell: Tunnell's converse in the odd case for $n\le 100$
-- statement:
--   This is the converse of Tunnell's criterion, in the odd case, for all $n\le100$.
--
--   Let $n\le100$ be an odd squarefree positive integer and put
--
--   $$
--   A(n)=\#\{(x,y,z)\in\mathbb Z^3:\ n=2x^2+y^2+32z^2\},\qquad B(n)=\#\{(x,y,z)\in\mathbb Z^3:\ n=2x^2+y^2+8z^2\}.
--   $$
--
--   If $2A(n)=B(n)$, then the elliptic curve $y^2=x^3-n^2x$ has a rational point with $y\neq0$, so $n$ is a congruent number.
--
--   Tunnell proved that every congruent $n$ satisfies $2A(n)=B(n)$, and that the converse follows from the Birch–Swinnerton-Dyer conjecture; the converse is open in general. Here it is established unconditionally for odd $n\le100$: the identity holds for exactly the twenty-four values $5,7,13,15,21,23,29,31,37,39,41,47,53,55,61,65,69,71,77,79,85,87,93,95$, and an explicit rational point is given for each (for instance $(45,300)$ for $n=5$). Together with the even case, Tunnell's converse is thereby verified for every squarefree $n\le100$.
--
--   **Formalization Note** The counts are `Set.ncard` of integer solution sets, as in the parent statement; for the other odd squarefree $n\le100$ the identity fails and the implication holds vacuously.
--
--   **Why this is a variation.** This varies the open converse of Tunnell's theorem on congruent numbers (`Tunnell.odd_count_implies_curve_point`): if the counting identity holds for an odd squarefree $n$, then $y^2=x^3-n^2x$ has a nonzero rational point. Tunnell proved the converse only conditionally on the Birch–Swinnerton-Dyer conjecture; this is the unconditional partial result for all odd squarefree $n\le 100$. It checks the converse on the first range of the congruent number problem, where the identity holds for exactly twenty-four values, each with an explicit rational point.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. B. Tunnell, A classical Diophantine problem and modular forms of weight 3/2, Invent. Math. 72 (1983), 323–334 (if n is congruent then the counting identity holds; the converse follows from the Birch–Swinnerton-Dyer conjecture); N. Koblitz, Introduction to Elliptic Curves and Modular Forms, 2nd ed., Springer GTM 97, 1993. Parent problem: Tunnell.odd_count_implies_curve_point.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Tunnell's odd-case count identity implies a nonzero rational point on `y² = x³ - n²x`,
for every squarefree odd `n ≤ 100` (finite verification; the identity `2·#{n = 2x²+y²+32z²} =
#{n = 2x²+y²+8z²}` holds exactly for `n ∈ {5, 7, 13, 15, 21, 23, 29, 31, 37, 39, 41, 47, 53, 55,
61, 65, 69, 71, 77, 79, 85, 87, 93, 95}`, all congruent numbers; Tunnell 1983, Conrad's notes,
Thm 4.1 and 4.11). -/
theorem tunnell_odd_count_implies_curve_point_le_100 (n : ℕ) (hn : n ≤ 100)
    (hsqf : Squarefree n) (hparity : Odd n) :
    2 * ({(x, y, z) : ℤ × ℤ × ℤ | (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2} :
        Set (ℤ × ℤ × ℤ)).ncard =
      ({(x, y, z) : ℤ × ℤ × ℤ | (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2} :
        Set (ℤ × ℤ × ℤ)).ncard →
    ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := by
  sorry

end LefebvreVariations
