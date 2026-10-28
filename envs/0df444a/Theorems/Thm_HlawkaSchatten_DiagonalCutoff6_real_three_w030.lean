-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_real_three_w030
-- name    : HlawkaSchatten.DiagonalCutoff6.real_three_w030
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:48:08.355243+00:00
-- url     : https://prove2.me/theorems/48a3d468-1e1a-4e85-9bb1-c7f700e84a1b
-- title:
--   Sharp real-three-dimensional Hlawka constant for 13/2 <= p <= 209/32
-- statement:
--   For $p\in[13/2,209/32]$ and $x,y,z\in\mathbb R^3$, let $S=\|x\|_p+\|y\|_p+\|z\|_p$, $T=\|x+y+z\|_p$, and $G=2S-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Then $$S-T\le K_pG,$$ where $K_p$ is the campaign cyclic constant.
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.real_three_w030 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (209/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
