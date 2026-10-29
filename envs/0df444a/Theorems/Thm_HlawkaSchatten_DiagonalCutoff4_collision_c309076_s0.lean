-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309076_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309076_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:42:45.758366+00:00
-- url     : https://prove2.me/theorems/0fc0baf5-f95d-43ec-82b9-2163132ab4bc
-- title:
--   Hlawka collision chart 309077, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309076_s0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : (0 : ℝ) ≤ ((2129/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2129/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-42857/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-42857/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3649/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3649/4000 : ℝ)*X 1 2) := by sorry
