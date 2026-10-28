-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10055_s8
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10055_s8
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:23:14.120039+00:00
-- url     : https://prove2.me/theorems/b0639499-7162-4aa7-ae14-2d22bd08f392
-- title:
--   Hlawka collision chart 10056, bounded proof step 9
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10055_s8 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev7 : (0 : ℝ) ≤ ((78103/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78103/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38401/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38401/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77421/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(77421/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14063/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14063/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34879/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34879/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35561/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35561/50000 : ℝ)*X 1 2) := by sorry
