-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1149
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1149
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:34:22.681564+00:00
-- url     : https://prove2.me/theorems/d7eb17af-16f5-458b-a0f4-9309a7cf845e
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8341/2048 ≤ p ≤ 4171/1024
-- statement:
--   For every real p in [8341/2048,4171/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1149 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
