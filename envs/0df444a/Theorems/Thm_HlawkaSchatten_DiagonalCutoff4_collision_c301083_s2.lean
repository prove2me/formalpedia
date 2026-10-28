-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301083_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301083_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:43:54.205599+00:00
-- url     : https://prove2.me/theorems/e8a9d925-8180-465d-bef0-dda76fb02f15
-- title:
--   Hlawka collision chart 301084, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301083_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((69133/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69133/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((37611/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(37611/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19829/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19829/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48667/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48667/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((11897/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(11897/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27193/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27193/50000 : ℝ)*X 1 2) := by sorry
