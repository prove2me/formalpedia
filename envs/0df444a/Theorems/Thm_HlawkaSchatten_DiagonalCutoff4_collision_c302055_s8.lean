-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302055_s8
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302055_s8
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:21:03.976619+00:00
-- url     : https://prove2.me/theorems/d8bd4111-fd6e-4a53-8c90-f1c058737ce4
-- title:
--   Hlawka collision chart 302056, bounded proof step 9
-- statement:
--   For the normalized ordered chart on $[65/16,131/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302055_s8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev7 : (0 : ℝ) ≤ ((1099/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1099/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28277/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28277/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27869/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27869/100000 : ℝ)*X 1 2)) : False := by sorry
