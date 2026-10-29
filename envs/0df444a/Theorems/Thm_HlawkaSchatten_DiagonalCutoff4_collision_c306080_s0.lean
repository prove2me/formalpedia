-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306080_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c306080_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:39:35.74225+00:00
-- url     : https://prove2.me/theorems/fd1d4453-79ba-4348-a79b-bd6783b55b9c
-- title:
--   Hlawka collision chart 306081, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[67/16,135/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c306080_s0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : (0 : ℝ) ≤ ((87939/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87939/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((16009/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(16009/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47363/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(47363/50000 : ℝ)*X 1 2) := by sorry
