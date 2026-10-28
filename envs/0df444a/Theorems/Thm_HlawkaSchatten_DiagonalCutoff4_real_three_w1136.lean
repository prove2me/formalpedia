-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1136
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1136
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:28:31.067333+00:00
-- url     : https://prove2.me/theorems/d94002c5-d510-4340-a4c5-f10f06fd5f1e
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 1041/256 ≤ p ≤ 8329/2048
-- statement:
--   For every real p in [1041/256,8329/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1136 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
