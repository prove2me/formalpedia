-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10023_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10023_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:10:37.144883+00:00
-- url     : https://prove2.me/theorems/058c17a6-f15a-4da2-bbd5-d5543c7b8073
-- title:
--   Hlawka collision chart 10024, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10023_s5 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((851/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(851/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2343/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2343/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21073/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21073/100000 : ℝ)*X 1 2)) : False := by sorry
