-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1631
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1631
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:10:33.423398+00:00
-- url     : https://prove2.me/theorems/c4a5fa42-2d23-407e-828e-1e17e12be961
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4839/1024 ≤ p ≤ 4843/1024
-- statement:
--   For every real p in [4839/1024,4843/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1631 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
