-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1364
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1364
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:08:14.490463+00:00
-- url     : https://prove2.me/theorems/0817e72c-3ee8-4f1e-9867-0caf47e1ee71
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4323/1024 ≤ p ≤ 1081/256
-- statement:
--   For every real p in [4323/1024,1081/256], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1364 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
