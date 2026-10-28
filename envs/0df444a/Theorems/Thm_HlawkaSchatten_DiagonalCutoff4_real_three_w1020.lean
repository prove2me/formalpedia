-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1020
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1020
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:17:29.064802+00:00
-- url     : https://prove2.me/theorems/1822ff01-2ff4-44e8-b160-d01513d9b6a3
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 2053/512 ≤ p ≤ 8213/2048
-- statement:
--   For every real p in [2053/512,8213/2048], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1020 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
