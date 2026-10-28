-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1039
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1039
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:44:44.336639+00:00
-- url     : https://prove2.me/theorems/fcf5f8f6-7bdc-41ed-8ac6-e4b848e37906
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8231/2048 ≤ p ≤ 1029/256
-- statement:
--   For every real p in [8231/2048,1029/256], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1039 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
