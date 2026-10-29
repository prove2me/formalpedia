-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314086_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c314086_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:02:13.506149+00:00
-- url     : https://prove2.me/theorems/72c2c5c7-4e8d-4367-bc2d-8349ef8eb92a
-- title:
--   Hlawka collision chart 314087, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[37/8,75/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c314086_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((71317/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71317/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-81879/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-81879/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20471/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20471/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27867/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27867/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-58969/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-58969/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26317/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(26317/50000 : ℝ)*X 1 2) := by sorry
