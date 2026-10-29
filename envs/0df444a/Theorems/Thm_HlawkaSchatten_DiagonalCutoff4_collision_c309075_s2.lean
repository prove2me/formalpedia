-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309075_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309075_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:42:47.224998+00:00
-- url     : https://prove2.me/theorems/21843ba9-5e4c-496f-97be-d31ab1166db3
-- title:
--   Hlawka collision chart 309076, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309075_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((50519/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(50519/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-72023/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-72023/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1632/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1632/3125 : ℝ)*X 1 2)) : False := by sorry
