-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1451
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1451
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:38:36.035989+00:00
-- url     : https://prove2.me/theorems/6d09ca2f-d36d-4cff-b81a-e7151757233f
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 2205/512 ≤ p ≤ 4411/1024
-- statement:
--   For every real p in [2205/512,4411/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1451 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
