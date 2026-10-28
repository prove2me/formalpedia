-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1024
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1024
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:14:57.49599+00:00
-- url     : https://prove2.me/theorems/fbc8ec6b-eaf9-4ad2-80c8-c8f1ccc2646d
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 1027/256 ≤ p ≤ 8217/2048
-- statement:
--   For every real p in [1027/256,8217/2048], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1024 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
