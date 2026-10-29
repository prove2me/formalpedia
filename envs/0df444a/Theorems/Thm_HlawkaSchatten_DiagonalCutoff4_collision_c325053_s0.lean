-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c325053_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c325053_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:52:07.069999+00:00
-- url     : https://prove2.me/theorems/b35170fe-32e9-4c53-8ef8-8cec363b5ebd
-- title:
--   Hlawka collision chart 325054, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[85/16,87/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c325053_s0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : (0 : ℝ) ≤ ((67047/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67047/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4201/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4201/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65643/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65643/100000 : ℝ)*X 1 2) := by sorry
