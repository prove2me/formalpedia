-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s9
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304061_s9
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:35:17.893988+00:00
-- url     : https://prove2.me/theorems/26bc2161-08e1-44ce-bca1-5ca064622efd
-- title:
--   Hlawka collision chart 304062, bounded proof step 10
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304061_s9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev8 : (0 : ℝ) ≤ ((3979/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3979/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3961/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3961/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3653/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3653/20000 : ℝ)*X 1 2)) : False := by sorry
