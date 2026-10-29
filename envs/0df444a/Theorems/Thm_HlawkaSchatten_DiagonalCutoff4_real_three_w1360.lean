-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1360
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1360
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:00:51.527944+00:00
-- url     : https://prove2.me/theorems/5575c6ea-841d-4907-97c1-667b8b51cee5
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4319/1024 ≤ p ≤ 135/32
-- statement:
--   For every real p in [4319/1024,135/32], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1360 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
