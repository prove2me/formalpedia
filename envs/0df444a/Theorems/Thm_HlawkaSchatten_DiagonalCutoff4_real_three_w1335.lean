-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1335
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1335
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:44:16.92122+00:00
-- url     : https://prove2.me/theorems/5b39c0e2-9139-4e6a-a745-3aa0c033f2c1
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 2147/512 ≤ p ≤ 4295/1024
-- statement:
--   For every real p in [2147/512,4295/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1335 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
