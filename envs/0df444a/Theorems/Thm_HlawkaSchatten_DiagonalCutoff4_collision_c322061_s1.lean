-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c322061_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c322061_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:43:11.433899+00:00
-- url     : https://prove2.me/theorems/853e73f7-91cd-449e-aeee-6ac1977630fb
-- title:
--   Hlawka collision chart 322062, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[41/8,83/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c322061_s1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((71209/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71209/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35187/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35187/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65793/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65793/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17873/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17873/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42619/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(42619/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9531/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9531/25000 : ℝ)*X 1 2) := by sorry
