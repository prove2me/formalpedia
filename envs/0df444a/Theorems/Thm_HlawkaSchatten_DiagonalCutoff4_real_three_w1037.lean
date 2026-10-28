-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1037
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1037
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:44:06.027744+00:00
-- url     : https://prove2.me/theorems/1c5abb4d-3e5a-4d8a-9323-57fd35cd7efd
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8229/2048 ≤ p ≤ 4115/1024
-- statement:
--   For every real p in [8229/2048,4115/1024], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1037 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
