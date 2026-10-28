-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305059_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305059_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:57:05.97176+00:00
-- url     : https://prove2.me/theorems/d4d111c9-0c98-4012-bf53-c15ae393a4a1
-- title:
--   Hlawka collision chart 305060, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305059_s4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((75847/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75847/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2967/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2967/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(23991/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(23991/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12653/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12653/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49063/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(49063/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(631/3125 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(631/3125 : ℝ)*X 1 2) := by sorry
