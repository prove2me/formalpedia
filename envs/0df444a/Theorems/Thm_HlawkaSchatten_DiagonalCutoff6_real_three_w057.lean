-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_real_three_w057
-- name    : HlawkaSchatten.DiagonalCutoff6.real_three_w057
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:57:19.885436+00:00
-- url     : https://prove2.me/theorems/e1aab1ae-586e-462a-b9bb-9c4bef49b756
-- title:
--   Sharp real-three-dimensional Hlawka constant for 15/2 <= p <= 121/16
-- statement:
--   For $p\in[15/2,121/16]$ and $x,y,z\in\mathbb R^3$, let $S=\|x\|_p+\|y\|_p+\|z\|_p$, $T=\|x+y+z\|_p$, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then $$S-T\le K_pG,$$ where $K_p$ is the campaign cyclic constant.
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.real_three_w057 (p : ℝ) (hpa : (15/2 : ℝ) ≤ p) (hpb : p ≤ (121/16 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
