-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312062_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312062_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:23:41.265535+00:00
-- url     : https://prove2.me/theorems/e8823f94-edaf-4dd9-8450-f58c96a24f28
-- title:
--   Hlawka collision chart 312063, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312062_s3 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((2421/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2421/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19517/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19517/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25161/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-25161/100000 : ℝ)*X 1 2)) : False := by sorry
