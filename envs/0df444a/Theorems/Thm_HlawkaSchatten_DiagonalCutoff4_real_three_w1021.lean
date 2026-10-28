-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1021
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1021
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:17:57.398684+00:00
-- url     : https://prove2.me/theorems/b3a5fc5f-08d4-458d-9e9c-974159433cfe
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8213/2048 ≤ p ≤ 4107/1024
-- statement:
--   For every real p in [8213/2048,4107/1024], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1021 (p : ℝ) (hpa : (8213/2048 : ℝ) ≤ p) (hpb : p ≤ (4107/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
