-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1773
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1773
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:06:50.279305+00:00
-- url     : https://prove2.me/theorems/fe0d2cf3-6f7c-45c0-b9e4-f9503943c09e
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 6143/1024 ≤ p ≤ 6
-- statement:
--   For every real p in [6143/1024,6], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1773 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
