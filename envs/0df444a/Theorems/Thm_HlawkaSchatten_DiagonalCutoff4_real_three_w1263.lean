-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1263
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1263
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:41:45.623467+00:00
-- url     : https://prove2.me/theorems/179aa435-79b2-427f-be18-d50ebec7e417
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8455/2048 ≤ p ≤ 1057/256
-- statement:
--   For every real p in [8455/2048,1057/256], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1263 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
