-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1168
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1168
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:42:57.409778+00:00
-- url     : https://prove2.me/theorems/8ef53cad-67be-4fe6-8b9e-f826b083ee5d
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 1045/256 ≤ p ≤ 8361/2048
-- statement:
--   For every real p in [1045/256,8361/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1168 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
