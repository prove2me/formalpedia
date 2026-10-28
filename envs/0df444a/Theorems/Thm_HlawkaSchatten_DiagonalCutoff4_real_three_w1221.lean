-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1221
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1221
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:05:33.145362+00:00
-- url     : https://prove2.me/theorems/ba01ce74-4c70-4256-bdf1-9f408056199a
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8413/2048 ≤ p ≤ 4207/1024
-- statement:
--   For every real p in [8413/2048,4207/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1221 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
