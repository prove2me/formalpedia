-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1598
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1598
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T23:55:24.210696+00:00
-- url     : https://prove2.me/theorems/9d394cdf-0c29-4ff0-ab0f-b34473626871
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4707/1024 ≤ p ≤ 4711/1024
-- statement:
--   For every real p in [4707/1024,4711/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1598 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
