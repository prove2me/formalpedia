-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306059_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c306059_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:37:22.940417+00:00
-- url     : https://prove2.me/theorems/39373964-b289-4476-a5f5-d7fc01a61be6
-- title:
--   Hlawka collision chart 306060, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[67/16,135/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c306059_s5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((6247/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6247/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30713/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30713/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1711/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1711/20000 : ℝ)*X 1 2)) : False := by sorry
