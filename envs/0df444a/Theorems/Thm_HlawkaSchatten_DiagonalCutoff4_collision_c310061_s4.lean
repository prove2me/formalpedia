-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310061_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310061_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:58:30.857584+00:00
-- url     : https://prove2.me/theorems/b46bd114-373a-495c-b4cb-c3cf83d0abea
-- title:
--   Hlawka collision chart 310062, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[35/8,71/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310061_s4 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((1453/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1453/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21111/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21111/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19293/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19293/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5027/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(493/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(493/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22907/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22907/100000 : ℝ)*X 1 2) := by sorry
