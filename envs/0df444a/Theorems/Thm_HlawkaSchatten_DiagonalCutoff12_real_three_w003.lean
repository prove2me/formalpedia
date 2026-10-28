-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w003
-- name    : HlawkaSchatten.DiagonalCutoff12.real_three_w003
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T01:41:58.788468+00:00
-- url     : https://prove2.me/theorems/853570d5-8af7-47dd-ba83-126940883ef9
-- title:
--   Sharp real-three-dimensional Hlawka bound for 51/4 <= p <= 13
-- statement:
--   For every real exponent $p\in[51/4,13]$ and all $x,y,z\in\mathbb R^3$, let $S=\|x\|_p+\|y\|_p+\|z\|_p$, $T=\|x+y+z\|_p$, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then $S-T\le K_pG$, where $K_p$ is the maximum cyclic ratio from the diagonal Hlawka campaign. This is one of sixteen adjoining exponent intervals covering $[12,16]$.
-- source:
--   Sharp diagonal Hlawka cutoff-12 extension of https://prove2.me/theorems/7fe6f02d-65e5-4c21-9796-c83889b29b9d . The proof retains the total-norm/pair-main coupling during localization and uses the previously proved curvature criterion. Generic contributions by Ezzeri Esa, bwdaugherty and Yuxuan Xu retain their Apache-2.0 attribution.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff12.real_three_w003 (p : ℝ) (hpa : (51/4 : ℝ) ≤ p) (hpb : p ≤ (13 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
