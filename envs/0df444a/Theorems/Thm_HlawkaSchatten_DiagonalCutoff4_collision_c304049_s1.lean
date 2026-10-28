-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304049_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304049_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:30:40.397921+00:00
-- url     : https://prove2.me/theorems/4dbde038-a731-401f-9c02-4cecc403b3c6
-- title:
--   Hlawka collision chart 304050, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[33/8,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304049_s1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((88451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(88451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11057/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11057/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(24217/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(24217/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((71541/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71541/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35771/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35771/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(679/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(679/6250 : ℝ)*X 1 2) := by sorry
