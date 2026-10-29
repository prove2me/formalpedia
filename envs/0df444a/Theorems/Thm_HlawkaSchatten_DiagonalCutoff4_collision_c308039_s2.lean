-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308039_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c308039_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:21:21.072669+00:00
-- url     : https://prove2.me/theorems/96523acb-36e9-4109-b052-96769ef33086
-- title:
--   Hlawka collision chart 308040, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[17/4,35/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c308039_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((6059/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6059/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-14167/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-14167/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20873/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20873/50000 : ℝ)*X 1 2)) : False := by sorry
