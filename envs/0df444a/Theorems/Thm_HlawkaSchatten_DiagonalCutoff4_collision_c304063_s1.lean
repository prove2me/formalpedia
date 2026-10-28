-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304063_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304063_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:35:54.374302+00:00
-- url     : https://prove2.me/theorems/1ba3c656-a088-44ed-9987-1d3fb26b3140
-- title:
--   Hlawka collision chart 304064, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304063_s1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((19283/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19283/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(95789/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(95789/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18841/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18841/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((91711/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(91711/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18257/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18257/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22209/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22209/25000 : ℝ)*X 1 2) := by sorry
