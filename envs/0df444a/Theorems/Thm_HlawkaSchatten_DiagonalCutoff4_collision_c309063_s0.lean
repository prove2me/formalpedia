-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309063_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309063_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:42:36.378987+00:00
-- url     : https://prove2.me/theorems/3924dff6-84a6-4575-a821-9bbc1072878d
-- title:
--   Hlawka collision chart 309064, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309063_s0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((4517/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4517/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11221/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11221/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8791/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8791/10000 : ℝ)*X 1 2) := by sorry
