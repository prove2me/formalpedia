-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1300
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1300
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:24:32.454924+00:00
-- url     : https://prove2.me/theorems/7c0b7a5b-9968-4db2-9f48-1bb96d8b229d
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4259/1024 ≤ p ≤ 1065/256
-- statement:
--   For every real p in [4259/1024,1065/256], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1300 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
