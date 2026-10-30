-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1591
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1591
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:54:38.410999+00:00
-- url     : https://prove2.me/theorems/efe2da1d-737c-44ba-8f4a-a70f0b5e8259
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4679/1024 ≤ p ≤ 4683/1024
-- statement:
--   For every real p in [4679/1024,4683/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1591 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
