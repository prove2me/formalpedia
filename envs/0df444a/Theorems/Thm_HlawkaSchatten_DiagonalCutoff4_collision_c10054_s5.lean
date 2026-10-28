-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10054_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10054_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:21:50.990274+00:00
-- url     : https://prove2.me/theorems/6c65e694-56b3-4935-82c0-daaadc4ae4b9
-- title:
--   Hlawka collision chart 10055, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10054_s5 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev4 : (0 : ℝ) ≤ ((5789/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5789/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15237/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15237/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11127/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11127/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((38483/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38483/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2509/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2509/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13087/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13087/50000 : ℝ)*X 1 2) := by sorry
