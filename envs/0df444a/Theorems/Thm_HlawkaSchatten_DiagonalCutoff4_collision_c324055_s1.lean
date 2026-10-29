-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324055_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c324055_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:48:58.336499+00:00
-- url     : https://prove2.me/theorems/0e6d1f32-f388-481c-a782-092ee71a8766
-- title:
--   Hlawka collision chart 324056, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[21/4,85/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c324055_s1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((17319/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17319/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8259/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8259/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67249/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(67249/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18893/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18893/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38349/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38349/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38023/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38023/100000 : ℝ)*X 1 2) := by sorry
