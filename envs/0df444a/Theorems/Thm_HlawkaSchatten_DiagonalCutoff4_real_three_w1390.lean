-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1390
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1390
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:15:06.773983+00:00
-- url     : https://prove2.me/theorems/90858b4a-0b1b-4646-8b11-fafbebc78a14
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4349/1024 ≤ p ≤ 2175/512
-- statement:
--   For every real p in [4349/1024,2175/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1390 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
