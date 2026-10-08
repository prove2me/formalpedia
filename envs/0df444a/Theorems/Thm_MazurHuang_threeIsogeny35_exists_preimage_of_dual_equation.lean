-- Prove2me | Theorems.Thm_MazurHuang_threeIsogeny35_exists_preimage_of_dual_equation
-- name    : MazurHuang.threeIsogeny35_exists_preimage_of_dual_equation
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:05:57.777147+00:00
-- url     : https://prove2.me/theorems/174b1870-b252-49d8-a8fb-1e31b5fd508c
-- title:
--   Every affine rational point of t^2 = s^3 - 3(12s+1500)^2 is the image of a rational point under the 3-isogeny
-- statement:
--   Let $s, t \in \mathbb{Q}$ satisfy $t^2 = s^3 - 3(12s+1500)^2$. Then there are $x, y \in \mathbb{Q}$ with $x \neq 0$, $y^2 = x^3 + (4x+28)^2$ and
--   $$\frac{9x^3+192x^2+4032x+28224}{x^2} = s, \qquad \frac{27x^3y - 12096xy - 169344y}{x^3} = t .$$
--   In other words, every affine rational point of $E' : t^2 = s^3 - 3(12s+1500)^2$ is the image of a rational point of $E : y^2 = x^3+(4x+28)^2$ under the explicit $3$-isogeny $\varphi : E \to E'$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean (n35_dual_affine_has_three_isogeny_preimage and its inputs).

import Mathlib

theorem MazurHuang.threeIsogeny35_exists_preimage_of_dual_equation
    {s t : ℚ}
    (hdual : t ^ 2 = s ^ 3 - 3 * (12 * s + 1500) ^ 2) :
    ∃ x y : ℚ, x ≠ 0 ∧
      y ^ 2 = x ^ 3 + (4 * x + 28) ^ 2 ∧
      (9 * x ^ 3 + 192 * x ^ 2 + 4032 * x + 28224) / x ^ 2 = s ∧
      (27 * x ^ 3 * y - 12096 * x * y - 169344 * y) / x ^ 3 = t := by sorry
