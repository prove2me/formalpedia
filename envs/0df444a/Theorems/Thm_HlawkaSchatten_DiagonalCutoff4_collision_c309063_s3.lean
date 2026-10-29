-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309063_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309063_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:42:45.505972+00:00
-- url     : https://prove2.me/theorems/3a3a8819-fd15-46a1-adb5-3999b0769200
-- title:
--   Hlawka collision chart 309064, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309063_s3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((68201/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68201/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68561/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(68561/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32961/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32961/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27353/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27353/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55683/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(55683/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5333/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5333/10000 : ℝ)*X 1 2) := by sorry
