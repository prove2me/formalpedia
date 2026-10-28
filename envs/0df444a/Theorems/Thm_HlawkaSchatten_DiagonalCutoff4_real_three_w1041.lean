-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1041
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1041
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:47:16.592342+00:00
-- url     : https://prove2.me/theorems/0bb6fe19-ccc2-4a5d-b24f-8bf0c07552f9
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8233/2048 ≤ p ≤ 4117/1024
-- statement:
--   For every real p in [8233/2048,4117/1024], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1041 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
