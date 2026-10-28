-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1075
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1075
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:47:05.54171+00:00
-- url     : https://prove2.me/theorems/c016746a-5f28-4afe-8479-304c56376394
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8267/2048 ≤ p ≤ 2067/512
-- statement:
--   For every real p in [8267/2048,2067/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1075 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
