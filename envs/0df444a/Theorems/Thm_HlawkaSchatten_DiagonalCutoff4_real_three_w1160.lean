-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1160
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1160
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:38:38.078996+00:00
-- url     : https://prove2.me/theorems/0642edbc-164f-4108-93f3-63115cf32c4c
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 261/64 ≤ p ≤ 8353/2048
-- statement:
--   For every real p in [261/64,8353/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1160 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
