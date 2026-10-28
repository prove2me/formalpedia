-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1042
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1042
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:47:24.141988+00:00
-- url     : https://prove2.me/theorems/623e430f-63a3-4b0a-8800-402c17d8f3a7
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4117/1024 ≤ p ≤ 8235/2048
-- statement:
--   For every real p in [4117/1024,8235/2048], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1042 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
