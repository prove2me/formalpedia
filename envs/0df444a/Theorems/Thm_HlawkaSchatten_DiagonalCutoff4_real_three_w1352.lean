-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1352
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1352
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:58:11.835733+00:00
-- url     : https://prove2.me/theorems/8dc22b3e-2f40-473b-8af7-079464ab813a
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4311/1024 ≤ p ≤ 539/128
-- statement:
--   For every real p in [4311/1024,539/128], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1352 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
