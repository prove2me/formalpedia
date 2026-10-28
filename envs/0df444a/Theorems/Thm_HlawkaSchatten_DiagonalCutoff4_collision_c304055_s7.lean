-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s7
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304055_s7
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:32:59.752233+00:00
-- url     : https://prove2.me/theorems/b4e0b67f-c987-4ce2-aa19-938b09d2f74c
-- title:
--   Hlawka collision chart 304056, bounded proof step 8
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304055_s7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((13061/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13061/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13279/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13279/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54167/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(54167/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7001/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7001/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35929/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35643/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35643/100000 : ℝ)*X 1 2) := by sorry
