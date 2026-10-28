-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10076_s6
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10076_s6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:35:26.56027+00:00
-- url     : https://prove2.me/theorems/7f499e14-e5ec-446a-8fe8-82edb0fb9936
-- title:
--   Hlawka collision chart 10077, bounded proof step 7
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10076_s6 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((11461/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11461/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-833/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-833/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30949/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(30949/100000 : ℝ)*X 1 2)) : False := by sorry
