-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10061_s9
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10061_s9
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:28:51.675318+00:00
-- url     : https://prove2.me/theorems/7cccbdf1-2d99-4dc5-a3c9-fd6f09916a3b
-- title:
--   Hlawka collision chart 10062, bounded proof step 10
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10061_s9 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev8 : (0 : ℝ) ≤ ((17621/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17621/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14757/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14757/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8691/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8691/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((57391/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57391/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3179/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3179/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7257/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7257/12500 : ℝ)*X 1 2) := by sorry
