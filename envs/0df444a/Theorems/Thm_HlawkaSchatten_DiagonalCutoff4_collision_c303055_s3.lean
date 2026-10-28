-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303055_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303055_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:52:54.453737+00:00
-- url     : https://prove2.me/theorems/1a4bd8aa-d181-49b9-9d68-6c7a6794725e
-- title:
--   Hlawka collision chart 303056, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[131/32,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303055_s3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((82753/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82753/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10149/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10149/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80841/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80841/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((73627/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73627/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9033/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9033/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18287/25000 : ℝ)*X 1 2) := by sorry
