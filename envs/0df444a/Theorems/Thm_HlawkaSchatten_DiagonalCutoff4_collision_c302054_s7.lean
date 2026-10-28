-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302054_s7
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302054_s7
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:19:24.049394+00:00
-- url     : https://prove2.me/theorems/2d56e903-4e26-402e-be7a-07e35fd3a5ff
-- title:
--   Hlawka collision chart 302055, bounded proof step 8
-- statement:
--   For the normalized ordered chart on $[65/16,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302054_s7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev6 : (0 : ℝ) ≤ ((19983/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19983/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10483/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10483/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6661/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6661/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15511/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15511/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8239/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8239/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2109/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2109/20000 : ℝ)*X 1 2) := by sorry
