-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305082_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305082_s2
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:23:07.008441+00:00
-- url     : https://prove2.me/theorems/983d0306-734c-435a-8fac-0c3d1ac21bfe
-- title:
--   Hlawka collision chart 305083, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305082_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((33649/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33649/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((81227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(81227/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(68223/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(68223/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((409/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(409/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((28477/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(28477/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(17053/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(17053/100000 : ℝ)*X 1 2) := by sorry
