-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306060_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c306060_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:37:23.314985+00:00
-- url     : https://prove2.me/theorems/09ae9dc5-9927-405a-ac39-f71cb267bea5
-- title:
--   Hlawka collision chart 306061, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[67/16,135/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c306060_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((89009/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(89009/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44719/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44719/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-40361/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-40361/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4967/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4967/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2011/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2011/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-69243/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-69243/100000 : ℝ)*X 1 2) := by sorry
