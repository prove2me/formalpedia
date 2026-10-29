-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321054_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c321054_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:40:10.578299+00:00
-- url     : https://prove2.me/theorems/cf77385b-d6b4-4238-9bce-a6cd829fe005
-- title:
--   Hlawka collision chart 321055, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[81/16,83/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c321054_s0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : (0 : ℝ) ≤ ((34483/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34483/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36317/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-32093/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-32093/50000 : ℝ)*X 1 2) := by sorry
