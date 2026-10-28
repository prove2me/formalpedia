-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w009
-- name    : HlawkaSchatten.DiagonalCutoff12.real_three_w009
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T01:41:58.607282+00:00
-- url     : https://prove2.me/theorems/1bbd74f6-27b5-4004-b70e-160d8bb50d5c
-- title:
--   Sharp real-three-dimensional Hlawka bound for 57/4 <= p <= 29/2
-- statement:
--   For every real exponent $p\in[57/4,29/2]$ and all $x,y,z\in\mathbb R^3$, let $S=\|x\|_p+\|y\|_p+\|z\|_p$, $T=\|x+y+z\|_p$, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then $S-T\le K_pG$, where $K_p$ is the maximum cyclic ratio from the diagonal Hlawka campaign. This is one of sixteen adjoining exponent intervals covering $[12,16]$.
-- source:
--   Sharp diagonal Hlawka cutoff-12 extension of https://prove2.me/theorems/7fe6f02d-65e5-4c21-9796-c83889b29b9d . The proof retains the total-norm/pair-main coupling during localization and uses the previously proved curvature criterion. Generic contributions by Ezzeri Esa, bwdaugherty and Yuxuan Xu retain their Apache-2.0 attribution.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff12.real_three_w009 (p : ℝ) (hpa : (57/4 : ℝ) ≤ p) (hpb : p ≤ (29/2 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
