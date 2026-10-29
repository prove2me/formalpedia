-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1392
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1392
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:15:28.635988+00:00
-- url     : https://prove2.me/theorems/8f4d318b-45ed-40d7-9505-fade8d7ad401
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4351/1024 ≤ p ≤ 17/4
-- statement:
--   For every real p in [4351/1024,17/4], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1392 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
