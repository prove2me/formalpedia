-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10083_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10083_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:37:24.831024+00:00
-- url     : https://prove2.me/theorems/307231db-d6d8-41f3-a3a0-2c6af61b626a
-- title:
--   Hlawka collision chart 10084, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10083_s3 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((54241/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54241/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((53427/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(53427/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30897/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(30897/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3321/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3321/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((6091/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6091/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(239/800 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(239/800 : ℝ)*X 1 2) := by sorry
