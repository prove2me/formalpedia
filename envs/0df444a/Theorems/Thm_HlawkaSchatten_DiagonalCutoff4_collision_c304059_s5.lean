-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304059_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304059_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:34:03.53842+00:00
-- url     : https://prove2.me/theorems/a5324143-9bac-481c-bb60-acb629bf1a04
-- title:
--   Hlawka collision chart 304060, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304059_s5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((74203/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74203/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14459/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14459/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5417/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5417/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2381/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2381/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11599/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11599/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18399/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18399/100000 : ℝ)*X 1 2) := by sorry
