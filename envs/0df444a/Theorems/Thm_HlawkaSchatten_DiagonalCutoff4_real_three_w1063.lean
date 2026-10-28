-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1063
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1063
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:04:20.13157+00:00
-- url     : https://prove2.me/theorems/4852abc3-f6a8-4ddd-9921-401ebb1276d1
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8255/2048 ≤ p ≤ 129/32
-- statement:
--   For every real p in [8255/2048,129/32], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1063 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
