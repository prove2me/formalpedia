-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1268
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1268
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:47:43.963305+00:00
-- url     : https://prove2.me/theorems/24e59f67-b085-4fb0-9645-238411ec1970
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 2115/512 ≤ p ≤ 8461/2048
-- statement:
--   For every real p in [2115/512,8461/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1268 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
