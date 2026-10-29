-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1448
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1448
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:37:57.813822+00:00
-- url     : https://prove2.me/theorems/7a537b52-e1f2-44b5-952c-4d7829daa4fc
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4407/1024 ≤ p ≤ 551/128
-- statement:
--   For every real p in [4407/1024,551/128], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1448 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
