-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305083_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305083_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:23:09.699891+00:00
-- url     : https://prove2.me/theorems/0edb2714-e64d-4683-b45b-b0edf7ce859c
-- title:
--   Hlawka collision chart 305084, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305083_s1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((16603/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16603/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((88917/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(88917/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46433/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46433/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8417/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8417/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((17511/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(17511/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76733/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76733/100000 : ℝ)*X 1 2) := by sorry
