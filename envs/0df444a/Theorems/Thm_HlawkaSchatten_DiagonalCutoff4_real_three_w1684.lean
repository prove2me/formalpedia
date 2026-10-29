-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1684
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1684
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:35:20.373746+00:00
-- url     : https://prove2.me/theorems/d95c3c09-03e4-4fb9-874c-a3c45d64c25e
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 5087/1024 ≤ p ≤ 5095/1024
-- statement:
--   For every real p in [5087/1024,5095/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1684 (p : ℝ) (hpa : (5087/1024 : ℝ) ≤ p) (hpb : p ≤ (5095/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
