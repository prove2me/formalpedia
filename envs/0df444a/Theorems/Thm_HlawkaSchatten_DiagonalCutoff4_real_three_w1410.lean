-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1410
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1410
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:31:36.515944+00:00
-- url     : https://prove2.me/theorems/82c126a7-9204-4803-bb93-3b8bd7c2d7a2
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4369/1024 ≤ p ≤ 2185/512
-- statement:
--   For every real p in [4369/1024,2185/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1410 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
