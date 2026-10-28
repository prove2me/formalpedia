-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1280
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1280
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:50:57.898608+00:00
-- url     : https://prove2.me/theorems/1b70a971-b040-4fb7-a420-4f7ccb284cad
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4239/1024 ≤ p ≤ 265/64
-- statement:
--   For every real p in [4239/1024,265/64], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1280 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
