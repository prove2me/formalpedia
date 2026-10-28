-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303060_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303060_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:53:41.211376+00:00
-- url     : https://prove2.me/theorems/d160f739-34be-43cc-a08d-cf4f5097b3fd
-- title:
--   Hlawka collision chart 303061, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[131/32,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303060_s3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((79447/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79447/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40181/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40181/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-70187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-70187/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3157/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3157/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1574/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1574/3125 : ℝ)*X 1 2) := by sorry
