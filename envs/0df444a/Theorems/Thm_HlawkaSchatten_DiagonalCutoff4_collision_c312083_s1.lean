-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312083_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312083_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:24:20.334075+00:00
-- url     : https://prove2.me/theorems/dc08a997-2e6a-42f2-aa02-bc88543a9355
-- title:
--   Hlawka collision chart 312084, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312083_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((74003/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74003/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1893/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(1893/2500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40709/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40709/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((47343/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47343/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((20729/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(20729/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3251/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3251/6250 : ℝ)*X 1 2) := by sorry
