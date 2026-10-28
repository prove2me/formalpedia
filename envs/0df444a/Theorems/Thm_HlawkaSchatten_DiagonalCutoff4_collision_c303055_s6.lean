-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303055_s6
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303055_s6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:53:34.123344+00:00
-- url     : https://prove2.me/theorems/81051872-5129-4052-8285-0aaa8079a931
-- title:
--   Hlawka collision chart 303056, bounded proof step 7
-- statement:
--   For the normalized ordered chart on $[131/32,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303055_s6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((893/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(893/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22833/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22833/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45771/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(45771/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((357/1250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(357/1250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2939/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2939/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1159/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1159/4000 : ℝ)*X 1 2) := by sorry
