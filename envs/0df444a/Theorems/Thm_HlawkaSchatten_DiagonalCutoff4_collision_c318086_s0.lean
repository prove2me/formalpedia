-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318086_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c318086_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:29:34.952026+00:00
-- url     : https://prove2.me/theorems/e205bdc5-e465-40f9-8d14-96fff841ef3d
-- title:
--   Hlawka collision chart 318087, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[39/8,79/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c318086_s0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((3981/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3981/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-18901/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-18901/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3039/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3039/4000 : ℝ)*X 1 2) := by sorry
