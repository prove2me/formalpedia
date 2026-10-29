-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c319057_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c319057_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:33:49.199978+00:00
-- url     : https://prove2.me/theorems/ef608c2a-607b-40a1-a455-fcc74166c09d
-- title:
--   Hlawka collision chart 319058, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[79/16,5]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c319057_s2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((3193/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3193/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25507/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25507/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(541/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(541/100000 : ℝ)*X 1 2)) : False := by sorry
