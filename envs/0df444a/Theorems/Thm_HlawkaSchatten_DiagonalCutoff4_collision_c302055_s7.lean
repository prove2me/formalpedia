-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302055_s7
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302055_s7
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:20:56.338965+00:00
-- url     : https://prove2.me/theorems/28a58658-d2da-4466-bae1-cafad59aa007
-- title:
--   Hlawka collision chart 302056, bounded proof step 8
-- statement:
--   For the normalized ordered chart on $[65/16,131/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302055_s7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((2141/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2141/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43833/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43833/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43857/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43857/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1099/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1099/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28277/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28277/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27869/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27869/100000 : ℝ)*X 1 2) := by sorry
