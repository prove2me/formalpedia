-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305062_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305062_s4
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T16:57:45.376611+00:00
-- url     : https://prove2.me/theorems/2296a518-f4d0-4e4e-b2fb-e788733e7435
-- title:
--   Hlawka collision chart 305063, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305062_s4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((13143/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13143/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16511/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16511/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-46649/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-46649/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((40531/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40531/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4081/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4081/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6483/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6483/25000 : ℝ)*X 1 2) := by sorry
