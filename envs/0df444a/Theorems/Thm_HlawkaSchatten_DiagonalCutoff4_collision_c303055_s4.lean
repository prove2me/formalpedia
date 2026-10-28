-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303055_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303055_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:52:58.859227+00:00
-- url     : https://prove2.me/theorems/be5aaddd-2ccf-49e8-a00b-c52147f612a9
-- title:
--   Hlawka collision chart 303056, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[131/32,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303055_s4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((73627/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73627/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9033/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9033/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18287/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12257/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12257/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2457/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2457/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31331/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31331/50000 : ℝ)*X 1 2) := by sorry
