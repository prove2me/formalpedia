-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305080_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305080_s2
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:23:01.614913+00:00
-- url     : https://prove2.me/theorems/b3cce6dd-e1b8-4653-9f85-1c858b308559
-- title:
--   Hlawka collision chart 305081, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305080_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((36749/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36749/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((19471/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(19471/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41163/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41163/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8551/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8551/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((10557/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(10557/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(983/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(983/2000 : ℝ)*X 1 2) := by sorry
