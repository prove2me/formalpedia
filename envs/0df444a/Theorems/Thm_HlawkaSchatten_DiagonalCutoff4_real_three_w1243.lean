-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1243
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1243
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:13:43.951502+00:00
-- url     : https://prove2.me/theorems/c4e6c8ed-0caa-4238-89b2-1824007404b1
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8435/2048 ≤ p ≤ 2109/512
-- statement:
--   For every real p in [8435/2048,2109/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1243 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
