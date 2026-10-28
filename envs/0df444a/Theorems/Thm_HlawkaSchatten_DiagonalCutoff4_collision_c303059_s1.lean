-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303059_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303059_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:53:37.004985+00:00
-- url     : https://prove2.me/theorems/41641b15-b4ee-47e0-8722-4d2d3b69f28d
-- title:
--   Hlawka collision chart 303060, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[131/32,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303059_s1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((47621/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47621/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23829/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23829/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(22463/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(22463/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8897/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8897/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(88939/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(88939/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(77511/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(77511/100000 : ℝ)*X 1 2) := by sorry
