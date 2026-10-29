-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307086_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c307086_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:06:06.828335+00:00
-- url     : https://prove2.me/theorems/b36575e5-f013-4bd4-9603-48496da6d955
-- title:
--   Hlawka collision chart 307087, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[135/32,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c307086_s3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((1536/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1536/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-73807/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-73807/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1749/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1749/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8133/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8133/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7813/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7813/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7847/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7847/25000 : ℝ)*X 1 2) := by sorry
