-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1143
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1143
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:31:27.646657+00:00
-- url     : https://prove2.me/theorems/68c6b0c9-c648-4638-afbe-0c0cd87a33e6
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8335/2048 ≤ p ≤ 521/128
-- statement:
--   For every real p in [8335/2048,521/128], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1143 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
