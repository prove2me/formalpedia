-- Prove2me | Theorems.Thm_MazurHuang_eisensteinDescent35_dualA_cube_class
-- name    : MazurHuang.eisensteinDescent35_dualA_cube_class
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:32.4674+00:00
-- url     : https://prove2.me/theorems/84431e2c-78a6-4df1-a1d8-abfc61b8ce5a
-- title:
--   The Eisenstein descent element of t^2 = s^3 - 3(12s+1500)^2 is a cube up to a cube root of unity
-- statement:
--   Let $\mathcal{O} = \mathbb{Z}[\omega]$ be the ring of integers of $\mathbb{Q}(\zeta_3)$ and $\sqrt{-3} = 2\omega+1$. Let $m, n, d$ be integers with $d > 0$, $\gcd(m,d) = 1$ and
--   $$n^2 = m^3 - 3d^2(12m + 1500d^2)^2 .$$
--   Then the element $A = n - \sqrt{-3}\,d\,(12m+1500d^2)$ of $\mathcal{O}$ has one of the forms $B^3$, $\omega B^3$, $\omega^2 B^3$ with $B \in \mathcal{O}$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean (n35DualA_three_cubeclasses and its inputs).

import Mathlib
import Definitions.Def_MazurHuang_EisensteinDescent35

open MazurHuang.EisensteinDescent35

theorem MazurHuang.eisensteinDescent35_dualA_cube_class
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 - 3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    (∃ B : N35O3, n35DualA m n d = B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit * B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit ^ 2 * B ^ 3) := by sorry
