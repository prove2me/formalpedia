-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309058_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309058_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:41:28.941158+00:00
-- url     : https://prove2.me/theorems/d5ab8a52-4270-4cbc-b061-26346a154cd1
-- title:
--   Hlawka collision chart 309059, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309058_s0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]]) : (0 : ℝ) ≤ ((92119/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92119/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8509/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8509/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1589/2000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1589/2000 : ℝ)*X 1 2) := by sorry
