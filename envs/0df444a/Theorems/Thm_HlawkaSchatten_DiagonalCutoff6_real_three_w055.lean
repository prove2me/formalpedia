-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_real_three_w055
-- name    : HlawkaSchatten.DiagonalCutoff6.real_three_w055
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:55:45.002628+00:00
-- url     : https://prove2.me/theorems/04c3b026-cd67-432c-b256-118f6f47aec5
-- title:
--   Sharp real-three-dimensional Hlawka constant for 59/8 <= p <= 119/16
-- statement:
--   For $p\in[59/8,119/16]$ and $x,y,z\in\mathbb R^3$, let $S=\|x\|_p+\|y\|_p+\|z\|_p$, $T=\|x+y+z\|_p$, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then $$S-T\le K_pG,$$ where $K_p$ is the campaign cyclic constant.
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.real_three_w055 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (119/16 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
