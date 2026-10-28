-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1211
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1211
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:01:46.707667+00:00
-- url     : https://prove2.me/theorems/6310b4b4-d991-4833-86ff-486cc525c8fb
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8403/2048 ≤ p ≤ 2101/512
-- statement:
--   For every real p in [8403/2048,2101/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1211 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
