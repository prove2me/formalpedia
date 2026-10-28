-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301053_s8
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301053_s8
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:31:17.337986+00:00
-- url     : https://prove2.me/theorems/2b98467c-a207-4c9e-8dd6-c55649068cb8
-- title:
--   Hlawka collision chart 301054, bounded proof step 9
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301053_s8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev7 : (0 : ℝ) ≤ ((31407/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31407/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7221/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7221/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8701/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8701/25000 : ℝ)*X 1 2)) : False := by sorry
