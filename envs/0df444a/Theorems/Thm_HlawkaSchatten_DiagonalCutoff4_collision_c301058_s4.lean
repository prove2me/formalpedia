-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301058_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301058_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:34:55.251538+00:00
-- url     : https://prove2.me/theorems/e7a58857-19c9-4a6d-b151-46b2e51dd225
-- title:
--   Hlawka collision chart 301059, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301058_s4 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((25211/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25211/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21733/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21733/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-19721/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-19721/100000 : ℝ)*X 1 2)) : False := by sorry
