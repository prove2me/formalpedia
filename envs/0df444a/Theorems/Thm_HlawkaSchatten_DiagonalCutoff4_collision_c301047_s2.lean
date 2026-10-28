-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301047_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301047_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:26:54.432929+00:00
-- url     : https://prove2.me/theorems/2f675f4f-7e0b-4c40-a77c-060ad14eb1d2
-- title:
--   Hlawka collision chart 301048, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301047_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((29891/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29891/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-951/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-951/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4829/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4829/6250 : ℝ)*X 1 2)) : False := by sorry
