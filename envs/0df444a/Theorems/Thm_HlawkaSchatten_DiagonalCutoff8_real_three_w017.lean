-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w017
-- name    : HlawkaSchatten.DiagonalCutoff8.real_three_w017
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T15:35:20.941535+00:00
-- url     : https://prove2.me/theorems/c30af270-bcd7-4ac8-9dbd-0ab1d01a31aa
-- title:
--   Sharp real-three-dimensional Hlawka bound for 73/8 <= p <= 37/4
-- statement:
--   For $p\in[73/8,37/4]$ and $x,y,z\in\mathbb R^3$, let $S$ be the sum of their $\ell_p$ norms, $T$ the norm of their total, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then
--   $$S-T\le K_pG,$$
--   where $K_p$ is the campaign cyclic constant. This is one of 32 adjoining intervals covering $[8,12]$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Generic norm, Bernoulli, permutation and Hessian arguments retain the Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff8.real_three_w017 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
