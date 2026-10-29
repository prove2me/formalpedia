-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314060_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c314060_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:01:12.818524+00:00
-- url     : https://prove2.me/theorems/8425b717-64bf-4459-afc5-ab4f37b3fcc8
-- title:
--   Hlawka collision chart 314061, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[37/8,75/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c314060_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((82361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81997/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(81997/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2289/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2289/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((57661/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57661/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1203/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1203/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8961/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8961/20000 : ℝ)*X 1 2) := by sorry
