-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1146
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1146
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:33:05.551302+00:00
-- url     : https://prove2.me/theorems/72b05d60-63eb-4d1c-93d6-5d51d033d05b
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4169/1024 ≤ p ≤ 8339/2048
-- statement:
--   For every real p in [4169/1024,8339/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1146 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
