-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1422
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1422
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:33:43.58732+00:00
-- url     : https://prove2.me/theorems/36224562-c7d1-4b9e-a9b1-bd65828883a1
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4381/1024 ≤ p ≤ 2191/512
-- statement:
--   For every real p in [4381/1024,2191/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1422 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
