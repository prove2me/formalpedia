-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1177
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1177
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:47:27.186981+00:00
-- url     : https://prove2.me/theorems/ee2b2c3f-f5f0-4ec4-bc4f-b78b2e6ca076
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8369/2048 ≤ p ≤ 4185/1024
-- statement:
--   For every real p in [8369/2048,4185/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1177 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
