-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w022
-- name    : HlawkaSchatten.DiagonalCutoff8.real_three_w022
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T15:35:19.960985+00:00
-- url     : https://prove2.me/theorems/ffa4d611-749b-43c7-a3d1-1e630d46c3d9
-- title:
--   Sharp real-three-dimensional Hlawka bound for 39/4 <= p <= 79/8
-- statement:
--   For $p\in[39/4,79/8]$ and $x,y,z\in\mathbb R^3$, let $S$ be the sum of their $\ell_p$ norms, $T$ the norm of their total, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then
--   $$S-T\le K_pG,$$
--   where $K_p$ is the campaign cyclic constant. This is one of 32 adjoining intervals covering $[8,12]$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Generic norm, Bernoulli, permutation and Hessian arguments retain the Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff8.real_three_w022 (p : ℝ) (hpa : (39/4 : ℝ) ≤ p) (hpb : p ≤ (79/8 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
