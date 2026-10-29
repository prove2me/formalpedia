-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329061_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c329061_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:03:42.505249+00:00
-- url     : https://prove2.me/theorems/f79d0c84-662a-4f67-b626-1f62c7c80f47
-- title:
--   Hlawka collision chart 329062, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[93/16,95/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c329061_s0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : (0 : ℝ) ≤ ((60861/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60861/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60543/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13897/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13897/25000 : ℝ)*X 1 2) := by sorry
