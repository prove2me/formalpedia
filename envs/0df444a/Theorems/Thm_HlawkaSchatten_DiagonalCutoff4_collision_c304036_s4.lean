-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304036_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304036_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:29:28.270563+00:00
-- url     : https://prove2.me/theorems/e21d5609-35dd-442c-bb84-f2ab9823f9fc
-- title:
--   Hlawka collision chart 304037, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[33/8,17/4]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304036_s4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((9/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1269/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-1269/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-12693/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-12693/100000 : ℝ)*X 1 2)) : False := by sorry
