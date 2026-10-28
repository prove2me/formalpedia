-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1256
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1256
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:38:26.116771+00:00
-- url     : https://prove2.me/theorems/1bd70bed-c0d0-4c1e-a418-2837293616f4
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 33/8 ≤ p ≤ 8449/2048
-- statement:
--   For every real p in [33/8,8449/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1256 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
