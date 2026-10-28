-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305060_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305060_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:57:24.157383+00:00
-- url     : https://prove2.me/theorems/6378b34e-dd5d-4f16-804b-2d31b24ab9e1
-- title:
--   Hlawka collision chart 305061, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305060_s5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev4 : (0 : ℝ) ≤ ((4789/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4789/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25967/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25967/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7097/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7097/20000 : ℝ)*X 1 2)) : False := by sorry
