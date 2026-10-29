-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c311053_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c311053_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:06:42.335416+00:00
-- url     : https://prove2.me/theorems/23cc6ea4-55e8-49de-8581-f5c4f62dcdb4
-- title:
--   Hlawka collision chart 311054, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[71/16,9/2]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c311053_s1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((3437/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3437/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43317/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17147/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17147/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((68329/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68329/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72817/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72817/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71719/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71719/100000 : ℝ)*X 1 2) := by sorry
