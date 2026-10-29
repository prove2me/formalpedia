-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c320087_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c320087_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:37:38.743721+00:00
-- url     : https://prove2.me/theorems/ed89954a-dac2-4c1e-a3ba-c8d47e100693
-- title:
--   Hlawka collision chart 320088, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[5,81/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c320087_s0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((69679/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69679/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((69679/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(69679/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69679/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69679/100000 : ℝ)*X 1 2) := by sorry
