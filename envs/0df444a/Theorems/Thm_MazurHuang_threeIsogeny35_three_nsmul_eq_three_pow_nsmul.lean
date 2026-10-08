-- Prove2me | Theorems.Thm_MazurHuang_threeIsogeny35_three_nsmul_eq_three_pow_nsmul
-- name    : MazurHuang.threeIsogeny35_three_nsmul_eq_three_pow_nsmul
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:17.975205+00:00
-- url     : https://prove2.me/theorems/10701d87-574c-4a43-a188-39b7d381cbd9
-- title:
--   On y^2 = x^3 + (4x+28)^2 the point 3P is divisible by every power of 3 inside 3E(Q)
-- statement:
--   Let $P$ be a rational point of $E : y^2 = x^3 + (4x+28)^2$. For every natural number $n$ there is a rational point $Q$ of $E$ with
--   $$3P = 3^n\,(3Q) .$$
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135.lean (exists_dualThreeIsogeny_preimage_of_alpha_cube) and FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean (E35_weak_three_descent, E35_three_nsmul_three_power_divisible).

import Mathlib
import Definitions.Def_MazurHuang_ThreeIsogeny35

open MazurHuang.ThreeIsogeny35

theorem MazurHuang.threeIsogeny35_three_nsmul_eq_three_pow_nsmul
    (P : E35ShortPoint) (n : ℕ) :
    ∃ Q : E35ShortPoint, 3 • P = (3 ^ n : ℕ) • (3 • Q) := by sorry
