-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10053_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10053_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:20:42.635677+00:00
-- url     : https://prove2.me/theorems/7b86e11f-5e7a-4720-9960-e26ff89ac526
-- title:
--   Hlawka collision chart 10054, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10053_s4 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((5493/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5493/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91637/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91637/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91211/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(91211/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16819/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16819/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(88483/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(88483/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(87901/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(87901/100000 : ℝ)*X 1 2) := by sorry
