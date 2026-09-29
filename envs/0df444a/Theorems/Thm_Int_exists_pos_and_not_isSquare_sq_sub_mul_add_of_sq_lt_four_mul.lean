-- Prove2me | Theorems.Thm_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul
-- name    : Int.exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/5acf50a6-0c40-5f2c-bfa7-2bd8d08b491d
-- title:
--   A non-square positive value of k²-tk+n
-- statement:
--   Let $t$ and $n$ be integers satisfying $t^2 < 4n$. The assertion is that there exists an integer $k$ such that the integer $k^2 - tk + n$ is strictly positive and is not a square in $\mathbb{Z}$, where being a square means being of the form $s \cdot s$ for some integer $s$ (Mathlib's `IsSquare`). Thus the quadratic $X^2 - tX + n$, assumed to have negative discriminant $t^2 - 4n$, takes at least one positive non-square value at an integer argument. No further hypotheses are imposed: $t$ and $n$ are arbitrary integers subject only to $t^2 < 4n$, and the conclusion is a pure existence statement, with no bound on or explicit description of the witness $k$ in the statement itself.
--
--   An elementary integrality statement about values of an integral quadratic with negative discriminant. It is used in the Čerednik–Drinfel'd material on fake elliptic curves, where an endomorphism $\varphi$ satisfying $\varphi^2 - t\varphi + n = 0$ is replaced by $\varphi - [k]$, so arranged that its reduced norm $k^2 - tk + n$ is positive and not a square.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Int.exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul
    (t n : ℤ) (htn : t ^ 2 < 4 * n) :
    ∃ k : ℤ, 0 < k ^ 2 - t * k + n ∧ ¬ IsSquare (k ^ 2 - t * k + n) := by sorry
