-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308080_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c308080_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:25:37.596992+00:00
-- url     : https://prove2.me/theorems/be3a33f8-f010-42fe-a700-4a90012a9089
-- title:
--   Hlawka collision chart 308081, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[17/4,69/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c308080_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((10817/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10817/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((31119/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(31119/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93009/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(93009/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33971/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33971/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((30947/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(30947/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19013/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19013/25000 : ℝ)*X 1 2) := by sorry
