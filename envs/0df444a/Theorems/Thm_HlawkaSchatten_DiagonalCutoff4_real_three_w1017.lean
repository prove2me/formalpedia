-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1017
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1017
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:17:26.676466+00:00
-- url     : https://prove2.me/theorems/e8e869a0-809f-486f-8e08-974bdc54a667
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8209/2048 ≤ p ≤ 4105/1024
-- statement:
--   For every real p in [8209/2048,4105/1024], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1017 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
