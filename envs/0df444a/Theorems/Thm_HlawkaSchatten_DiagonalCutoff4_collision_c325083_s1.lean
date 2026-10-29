-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c325083_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c325083_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:52:29.820979+00:00
-- url     : https://prove2.me/theorems/089bb976-e873-493f-9d2c-31a8c6ddca5e
-- title:
--   Hlawka collision chart 325084, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[85/16,87/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c325083_s1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((3711/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3711/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((56453/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(56453/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32099/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32099/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1107/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1107/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((2309/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(2309/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3741/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3741/20000 : ℝ)*X 1 2) := by sorry
