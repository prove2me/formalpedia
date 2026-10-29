-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316049_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c316049_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:14:07.778227+00:00
-- url     : https://prove2.me/theorems/57aeae02-420a-4bda-8209-002e8bef9d56
-- title:
--   Hlawka collision chart 316050, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[19/4,39/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c316049_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((72571/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72571/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72577/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72577/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16149/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16149/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((848/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(848/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(848/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(848/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(797/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(797/100000 : ℝ)*X 1 2) := by sorry
