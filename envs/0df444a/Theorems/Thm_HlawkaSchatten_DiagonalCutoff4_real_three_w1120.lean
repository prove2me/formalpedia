-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1120
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1120
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:07:35.364386+00:00
-- url     : https://prove2.me/theorems/042fb38f-2183-40eb-919a-0d2438154c51
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 1039/256 ≤ p ≤ 8313/2048
-- statement:
--   For every real p in [1039/256,8313/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1120 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
