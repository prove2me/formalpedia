-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1742
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1742
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:56:26.876289+00:00
-- url     : https://prove2.me/theorems/10e47d21-ac0d-4be0-87ac-76525c44dd7a
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 5631/1024 ≤ p ≤ 5647/1024
-- statement:
--   For every real p in [5631/1024,5647/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1742 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
