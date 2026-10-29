-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1388
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1388
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:14:54.079171+00:00
-- url     : https://prove2.me/theorems/c4321d7b-8d6f-42f3-b563-f2b7dcb2ad02
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4347/1024 ≤ p ≤ 1087/256
-- statement:
--   For every real p in [4347/1024,1087/256], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1388 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
