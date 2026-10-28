-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302055_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302055_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:20:17.618428+00:00
-- url     : https://prove2.me/theorems/18dea9a5-e2f5-4c2b-b3a8-88fd52f463e4
-- title:
--   Hlawka collision chart 302056, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[65/16,131/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302055_s1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((47953/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47953/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(96241/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(96241/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47299/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(47299/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5729/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5729/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45739/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45739/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44829/50000 : ℝ)*X 1 2) := by sorry
