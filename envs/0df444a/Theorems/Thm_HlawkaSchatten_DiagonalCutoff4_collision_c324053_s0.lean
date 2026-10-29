-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324053_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c324053_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:48:59.485759+00:00
-- url     : https://prove2.me/theorems/799aac3e-8e4d-4e71-b6e4-9ffc2278b40a
-- title:
--   Hlawka collision chart 324054, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[21/4,43/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c324053_s0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : (0 : ℝ) ≤ ((68197/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68197/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17081/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17081/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33393/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33393/50000 : ℝ)*X 1 2) := by sorry
