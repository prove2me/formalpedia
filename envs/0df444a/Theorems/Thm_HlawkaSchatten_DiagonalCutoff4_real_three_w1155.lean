-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1155
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1155
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:36:36.645047+00:00
-- url     : https://prove2.me/theorems/2588d9fb-5584-473a-8be6-1794519b8981
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8347/2048 ≤ p ≤ 2087/512
-- statement:
--   For every real p in [8347/2048,2087/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1155 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
