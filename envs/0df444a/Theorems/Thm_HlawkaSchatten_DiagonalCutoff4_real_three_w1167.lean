-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1167
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1167
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:42:15.066207+00:00
-- url     : https://prove2.me/theorems/9eed3f9a-8b73-4c56-afc0-412b73168ea0
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8359/2048 ≤ p ≤ 1045/256
-- statement:
--   For every real p in [8359/2048,1045/256], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1167 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
