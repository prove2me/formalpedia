-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312052_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312052_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:19:56.528986+00:00
-- url     : https://prove2.me/theorems/fbbba35e-0580-4f7a-ab10-5fc7001b2075
-- title:
--   Hlawka collision chart 312053, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[9/2,37/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312052_s0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : (0 : ℝ) ≤ ((7879/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7879/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40029/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40029/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-68093/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-68093/100000 : ℝ)*X 1 2) := by sorry
