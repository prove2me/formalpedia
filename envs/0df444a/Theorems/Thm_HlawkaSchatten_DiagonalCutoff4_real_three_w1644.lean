-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1644
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1644
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:19:18.252579+00:00
-- url     : https://prove2.me/theorems/0b6bdd5f-e83c-4e6f-8d2f-e8a95a00558d
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4891/1024 ≤ p ≤ 4895/1024
-- statement:
--   For every real p in [4891/1024,4895/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1644 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
