-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c328061_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c328061_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:01:19.473748+00:00
-- url     : https://prove2.me/theorems/abd76b8f-ac13-4d38-bff5-f55d4e5d6654
-- title:
--   Hlawka collision chart 328062, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[91/16,93/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c328061_s1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((62549/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62549/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12429/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12429/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57197/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57197/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11641/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11641/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29769/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29769/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27093/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27093/100000 : ℝ)*X 1 2) := by sorry
