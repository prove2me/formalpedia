-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s11
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10063_s11
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:30:28.167741+00:00
-- url     : https://prove2.me/theorems/f23209ee-d7ca-42c6-90dc-1be00d355576
-- title:
--   Hlawka collision chart 10064, bounded proof step 12
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10063_s11 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev10 : (0 : ℝ) ≤ ((36169/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36169/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9099/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9099/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35059/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35059/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((67769/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67769/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1711/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1711/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2059/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2059/3125 : ℝ)*X 1 2) := by sorry
