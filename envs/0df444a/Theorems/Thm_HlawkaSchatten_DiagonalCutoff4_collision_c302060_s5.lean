-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302060_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302060_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:23:51.75625+00:00
-- url     : https://prove2.me/theorems/f6209afd-7447-4b15-9288-87c946f980a4
-- title:
--   Hlawka collision chart 302061, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[65/16,131/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302060_s5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev4 : (0 : ℝ) ≤ ((26293/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26293/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56531/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9979/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9979/25000 : ℝ)*X 1 2)) : False := by sorry
