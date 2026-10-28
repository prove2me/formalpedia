-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1007
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1007
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:16:32.492485+00:00
-- url     : https://prove2.me/theorems/51099ead-e05b-41a7-a268-161916da618f
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8199/2048 ≤ p ≤ 1025/256
-- statement:
--   For every real p in [8199/2048,1025/256], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1007 (p : ℝ) (hpa : (8199/2048 : ℝ) ≤ p) (hpb : p ≤ (1025/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
