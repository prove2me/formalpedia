-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10082_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10082_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:37:27.023362+00:00
-- url     : https://prove2.me/theorems/d3f36cd7-9dd2-44a6-88ef-50ce545d24f8
-- title:
--   Hlawka collision chart 10083, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10082_s4 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((7889/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7889/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((9771/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(9771/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1411/4000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1411/4000 : ℝ)*X 1 2)) : False := by sorry
