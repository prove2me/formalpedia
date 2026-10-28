-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1162
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1162
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:39:40.106656+00:00
-- url     : https://prove2.me/theorems/dadc991e-dbca-4bf7-9a9d-7f8127aa4a6f
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4177/1024 ≤ p ≤ 8355/2048
-- statement:
--   For every real p in [4177/1024,8355/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1162 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
