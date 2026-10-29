-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307076_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c307076_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:03:55.300667+00:00
-- url     : https://prove2.me/theorems/ffffbaea-691e-436b-9a5b-606a9c573b05
-- title:
--   Hlawka collision chart 307077, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[135/32,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c307076_s0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : (0 : ℝ) ≤ ((17463/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17463/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-89791/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-89791/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93899/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(93899/100000 : ℝ)*X 1 2) := by sorry
