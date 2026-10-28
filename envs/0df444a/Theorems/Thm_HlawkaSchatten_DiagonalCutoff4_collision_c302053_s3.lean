-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302053_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302053_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:17:34.775592+00:00
-- url     : https://prove2.me/theorems/d9e752e8-f12a-469b-81a4-d89a285d0bb7
-- title:
--   Hlawka collision chart 302054, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[65/16,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302053_s3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((84841/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84841/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(88067/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(88067/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21857/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21857/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((78041/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78041/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20723/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20723/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82147/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(82147/100000 : ℝ)*X 1 2) := by sorry
