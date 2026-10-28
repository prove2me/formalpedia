-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w021
-- name    : HlawkaSchatten.DiagonalCutoff8.real_three_w021
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T15:35:23.223339+00:00
-- url     : https://prove2.me/theorems/7d0df822-0159-49ea-bc2d-67a4860db382
-- title:
--   Sharp real-three-dimensional Hlawka bound for 77/8 <= p <= 39/4
-- statement:
--   For $p\in[77/8,39/4]$ and $x,y,z\in\mathbb R^3$, let $S$ be the sum of their $\ell_p$ norms, $T$ the norm of their total, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then
--   $$S-T\le K_pG,$$
--   where $K_p$ is the campaign cyclic constant. This is one of 32 adjoining intervals covering $[8,12]$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Generic norm, Bernoulli, permutation and Hessian arguments retain the Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff8.real_three_w021 (p : ℝ) (hpa : (77/8 : ℝ) ≤ p) (hpb : p ≤ (39/4 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
