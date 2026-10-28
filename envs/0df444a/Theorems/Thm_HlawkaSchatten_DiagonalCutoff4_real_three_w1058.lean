-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1058
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1058
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:01:01.701855+00:00
-- url     : https://prove2.me/theorems/0c5710f5-0ee8-41a9-952d-3396ed168bdf
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4125/1024 ≤ p ≤ 8251/2048
-- statement:
--   For every real p in [4125/1024,8251/2048], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1058 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
