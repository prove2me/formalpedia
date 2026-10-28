-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1040
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1040
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:45:43.752342+00:00
-- url     : https://prove2.me/theorems/d9c408eb-11b9-4360-b2f1-d66a64722ebd
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 1029/256 ≤ p ≤ 8233/2048
-- statement:
--   For every real p in [1029/256,8233/2048], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1040 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
