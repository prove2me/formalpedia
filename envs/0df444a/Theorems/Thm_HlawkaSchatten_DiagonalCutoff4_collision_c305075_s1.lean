-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305075_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305075_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:22:45.463202+00:00
-- url     : https://prove2.me/theorems/28943f0a-6317-451f-86c3-06263b771369
-- title:
--   Hlawka collision chart 305076, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305075_s1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((82137/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82137/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-94069/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-94069/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5451/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5451/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((62453/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62453/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-41937/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-41937/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66019/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(66019/100000 : ℝ)*X 1 2) := by sorry
