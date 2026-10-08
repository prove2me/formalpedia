-- Prove2me | Theorems.Thm_MazurHuang_threeIsogeny35_three_nsmul_eq_zero_of_three_pow_divisible
-- name    : MazurHuang.threeIsogeny35_three_nsmul_eq_zero_of_three_pow_divisible
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:21.640154+00:00
-- url     : https://prove2.me/theorems/eda33143-7b0b-4241-be76-fa71e3eb7016
-- title:
--   On y^2 = x^3 + (4x+28)^2 a point 3P that is infinitely 3-divisible inside 3E(Q) is zero
-- statement:
--   Let $P$ be a rational point of $E : y^2 = x^3 + (4x+28)^2$. Suppose that for every natural number $n$ there is a rational point $Q$ of $E$ with $3P = 3^n(3Q)$. Then $3P = O$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean (E35_three_nsmul_formal, E35_formal_separated and their inputs).

import Mathlib
import Definitions.Def_MazurHuang_ThreeIsogeny35

open MazurHuang.ThreeIsogeny35

theorem MazurHuang.threeIsogeny35_three_nsmul_eq_zero_of_three_pow_divisible
    (P : E35ShortPoint)
    (h : ∀ n : ℕ, ∃ Q : E35ShortPoint, 3 • P = (3 ^ n : ℕ) • (3 • Q)) :
    3 • P = 0 := by sorry
