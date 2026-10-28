-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10029_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10029_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:11:38.375838+00:00
-- url     : https://prove2.me/theorems/8cc0247f-e320-4d6b-8636-9d6e4b408496
-- title:
--   Hlawka collision chart 10030, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10029_s0 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]]) : (0 : ℝ) ≤ ((50087/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(50087/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(957/4000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(957/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32461/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32461/50000 : ℝ)*X 1 2) := by sorry
