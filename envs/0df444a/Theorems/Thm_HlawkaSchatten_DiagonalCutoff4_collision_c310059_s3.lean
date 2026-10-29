-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310059_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310059_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:58:20.175201+00:00
-- url     : https://prove2.me/theorems/f306ad91-76f8-45d7-bf46-1b2bbe1e9da6
-- title:
--   Hlawka collision chart 310060, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[35/8,71/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310059_s3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((12343/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12343/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47503/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47503/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(19863/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(19863/100000 : ℝ)*X 1 2)) : False := by sorry
