-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1530
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1530
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:10:08.154194+00:00
-- url     : https://prove2.me/theorems/cd70c1ec-3a51-4120-be40-7d592c982ac9
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4555/1024 ≤ p ≤ 4557/1024
-- statement:
--   For every real p in [4555/1024,4557/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1530 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
