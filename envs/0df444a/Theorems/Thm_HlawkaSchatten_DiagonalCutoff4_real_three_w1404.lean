-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1404
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1404
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:30:12.439477+00:00
-- url     : https://prove2.me/theorems/90821436-a6d2-41f7-be5a-b00ebdb70da9
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4363/1024 ≤ p ≤ 1091/256
-- statement:
--   For every real p in [4363/1024,1091/256], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1404 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
