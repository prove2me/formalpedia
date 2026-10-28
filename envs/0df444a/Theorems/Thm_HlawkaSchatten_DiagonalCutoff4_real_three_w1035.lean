-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1035
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1035
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:41:54.757501+00:00
-- url     : https://prove2.me/theorems/d9d562c3-f1fc-4350-b5f4-98468efcf974
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8227/2048 ≤ p ≤ 2057/512
-- statement:
--   For every real p in [8227/2048,2057/512], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1035 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
