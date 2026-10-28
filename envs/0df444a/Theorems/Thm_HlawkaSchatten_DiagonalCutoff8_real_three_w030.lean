-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w030
-- name    : HlawkaSchatten.DiagonalCutoff8.real_three_w030
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T15:35:59.043376+00:00
-- url     : https://prove2.me/theorems/b16bc4eb-1568-42b1-b490-abc8bb96fac9
-- title:
--   Sharp real-three-dimensional Hlawka bound for 23/2 <= p <= 47/4
-- statement:
--   For $p\in[23/2,47/4]$ and $x,y,z\in\mathbb R^3$, let $S$ be the sum of their $\ell_p$ norms, $T$ the norm of their total, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then
--   $$S-T\le K_pG,$$
--   where $K_p$ is the campaign cyclic constant. This is one of 32 adjoining intervals covering $[8,12]$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Generic norm, Bernoulli, permutation and Hessian arguments retain the Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff8.real_three_w030 (p : ℝ) (hpa : (23/2 : ℝ) ≤ p) (hpb : p ≤ (47/4 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
