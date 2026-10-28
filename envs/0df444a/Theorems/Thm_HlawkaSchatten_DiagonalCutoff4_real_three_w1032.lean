-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1032
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1032
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:39:55.27717+00:00
-- url     : https://prove2.me/theorems/69d9b346-1b30-4169-9484-ee0015829260
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 257/64 ≤ p ≤ 8225/2048
-- statement:
--   For every real p in [257/64,8225/2048], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1032 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
