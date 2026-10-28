-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1252
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1252
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:16:29.22081+00:00
-- url     : https://prove2.me/theorems/892deb1c-35d5-48d9-949d-75e6d71a8947
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 2111/512 ≤ p ≤ 8445/2048
-- statement:
--   For every real p in [2111/512,8445/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1252 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
