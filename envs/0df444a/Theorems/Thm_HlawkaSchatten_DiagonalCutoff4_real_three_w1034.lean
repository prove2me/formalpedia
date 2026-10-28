-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1034
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1034
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:41:02.276082+00:00
-- url     : https://prove2.me/theorems/c31cc03d-ffc8-4b5f-8fc1-2672f3bef17a
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4113/1024 ≤ p ≤ 8227/2048
-- statement:
--   For every real p in [4113/1024,8227/2048], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1034 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
