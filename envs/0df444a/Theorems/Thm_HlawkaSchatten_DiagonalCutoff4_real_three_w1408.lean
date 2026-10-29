-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1408
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1408
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:31:26.215765+00:00
-- url     : https://prove2.me/theorems/9fed08d5-d8ed-4b65-8356-6cdd3cd8619f
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4367/1024 ≤ p ≤ 273/64
-- statement:
--   For every real p in [4367/1024,273/64], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1408 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
