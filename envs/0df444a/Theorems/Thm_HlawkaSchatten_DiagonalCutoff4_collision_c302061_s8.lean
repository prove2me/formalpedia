-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302061_s8
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302061_s8
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:24:00.715192+00:00
-- url     : https://prove2.me/theorems/fea601d1-0440-4c69-b9f8-03102a091422
-- title:
--   Hlawka collision chart 302062, bounded proof step 9
-- statement:
--   For the normalized ordered chart on $[65/16,131/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302061_s8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev7 : (0 : ℝ) ≤ ((9161/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9161/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22219/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22219/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(413/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(413/2000 : ℝ)*X 1 2)) : False := by sorry
