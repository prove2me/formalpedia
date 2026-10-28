-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304060_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304060_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:34:13.828885+00:00
-- url     : https://prove2.me/theorems/60fded45-5770-45ec-8644-8fbdc51b41af
-- title:
--   Hlawka collision chart 304061, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304060_s4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((16639/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16639/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10527/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10527/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73333/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-73333/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17889/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17889/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(921/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(921/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29713/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29713/50000 : ℝ)*X 1 2) := by sorry
