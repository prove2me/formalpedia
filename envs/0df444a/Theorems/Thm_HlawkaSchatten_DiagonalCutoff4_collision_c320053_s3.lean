-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c320053_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c320053_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:37:18.67108+00:00
-- url     : https://prove2.me/theorems/df385805-e18a-4faa-954f-e959d4c6806e
-- title:
--   Hlawka collision chart 320054, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[5,41/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c320053_s3 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((1179/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1179/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5911/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5911/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2879/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2879/12500 : ℝ)*X 1 2)) : False := by sorry
