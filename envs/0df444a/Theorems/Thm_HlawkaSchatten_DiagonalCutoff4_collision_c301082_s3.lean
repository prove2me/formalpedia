-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301082_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301082_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:42:55.019651+00:00
-- url     : https://prove2.me/theorems/d48cc0ac-5404-4b31-b592-6d9f596b14fa
-- title:
--   Hlawka collision chart 301083, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301082_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((9211/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9211/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((46423/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(46423/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3311/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3311/10000 : ℝ)*X 1 2)) : False := by sorry
