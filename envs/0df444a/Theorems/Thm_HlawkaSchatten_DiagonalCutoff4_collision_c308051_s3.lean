-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308051_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c308051_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:22:07.478153+00:00
-- url     : https://prove2.me/theorems/79713b7a-6199-4f60-a8d4-fdc72cb53a87
-- title:
--   Hlawka collision chart 308052, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[17/4,35/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c308051_s3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((29507/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29507/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14749/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14749/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(557/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(557/12500 : ℝ)*X 1 2)) : False := by sorry
