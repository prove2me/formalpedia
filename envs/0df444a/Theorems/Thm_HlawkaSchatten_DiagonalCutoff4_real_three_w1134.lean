-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1134
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1134
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:28:14.603376+00:00
-- url     : https://prove2.me/theorems/d716c105-f21d-4ef8-99f9-858f09bb801d
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4163/1024 ≤ p ≤ 8327/2048
-- statement:
--   For every real p in [4163/1024,8327/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1134 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
