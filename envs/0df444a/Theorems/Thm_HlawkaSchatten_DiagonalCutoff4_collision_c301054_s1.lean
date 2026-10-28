-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301054_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301054_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:31:19.298407+00:00
-- url     : https://prove2.me/theorems/747a8306-cbf6-4b33-8ce2-33af75f414d9
-- title:
--   Hlawka collision chart 301055, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301054_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((2391/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2391/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(96651/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(96651/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-84877/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-84877/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22139/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22139/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91247/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9253/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9253/12500 : ℝ)*X 1 2) := by sorry
