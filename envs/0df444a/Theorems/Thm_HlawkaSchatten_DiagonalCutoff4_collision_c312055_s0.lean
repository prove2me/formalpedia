-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312055_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312055_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:22:10.294007+00:00
-- url     : https://prove2.me/theorems/fc1a7a04-3c70-4413-9620-94ef50c0310e
-- title:
--   Hlawka collision chart 312056, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312055_s0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : (0 : ℝ) ≤ ((10693/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10693/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83709/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83709/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84141/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(84141/100000 : ℝ)*X 1 2) := by sorry
