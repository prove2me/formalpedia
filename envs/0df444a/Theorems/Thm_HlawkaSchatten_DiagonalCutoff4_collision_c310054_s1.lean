-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310054_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310054_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:57:03.325007+00:00
-- url     : https://prove2.me/theorems/2cb4fb7e-d080-480a-8fc8-390c956c3c38
-- title:
--   Hlawka collision chart 310055, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[35/8,71/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310054_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((10709/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10709/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44241/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44241/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-15701/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-15701/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13847/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13847/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36617/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36617/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-60771/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-60771/100000 : ℝ)*X 1 2) := by sorry
