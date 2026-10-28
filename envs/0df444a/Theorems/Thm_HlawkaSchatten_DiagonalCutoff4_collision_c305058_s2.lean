-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305058_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305058_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:56:48.050275+00:00
-- url     : https://prove2.me/theorems/11d1717a-91e8-4a47-a464-f57884dcb386
-- title:
--   Hlawka collision chart 305059, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305058_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((11111/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11111/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39933/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39933/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-70233/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-70233/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18423/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18423/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63329/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63329/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-10107/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-10107/25000 : ℝ)*X 1 2) := by sorry
