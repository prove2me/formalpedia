-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304053_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304053_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:31:55.650409+00:00
-- url     : https://prove2.me/theorems/e5afe7d1-4423-439a-9d3f-5ecb80b4d547
-- title:
--   Hlawka collision chart 304054, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[33/8,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304053_s4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((77983/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77983/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10457/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10457/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41409/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41409/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((68167/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68167/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76869/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76869/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76073/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76073/100000 : ℝ)*X 1 2) := by sorry
