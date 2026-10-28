-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305061_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305061_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:57:36.119825+00:00
-- url     : https://prove2.me/theorems/21a5c86a-03d6-42a6-948c-32f2d0f3993a
-- title:
--   Hlawka collision chart 305062, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305061_s4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((78471/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78471/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19971/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19971/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76537/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76537/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((67441/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67441/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7093/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7093/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32867/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32867/50000 : ℝ)*X 1 2) := by sorry
