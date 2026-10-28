-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w025
-- name    : HlawkaSchatten.DiagonalCutoff8.real_three_w025
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T15:36:02.744623+00:00
-- url     : https://prove2.me/theorems/d9452551-f675-4b31-94d6-29da5e44d13d
-- title:
--   Sharp real-three-dimensional Hlawka bound for 41/4 <= p <= 21/2
-- statement:
--   For $p\in[41/4,21/2]$ and $x,y,z\in\mathbb R^3$, let $S$ be the sum of their $\ell_p$ norms, $T$ the norm of their total, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then
--   $$S-T\le K_pG,$$
--   where $K_p$ is the campaign cyclic constant. This is one of 32 adjoining intervals covering $[8,12]$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Generic norm, Bernoulli, permutation and Hessian arguments retain the Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff8.real_three_w025 (p : ℝ) (hpa : (41/4 : ℝ) ≤ p) (hpb : p ≤ (21/2 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
