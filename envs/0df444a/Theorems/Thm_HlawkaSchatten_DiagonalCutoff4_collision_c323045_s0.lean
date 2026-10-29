-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c323045_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c323045_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:46:01.139109+00:00
-- url     : https://prove2.me/theorems/aff77158-44f9-4a1e-a542-bba4073be4e3
-- title:
--   Hlawka collision chart 323046, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[83/16,85/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c323045_s0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((47193/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47193/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-61507/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-61507/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69441/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69441/100000 : ℝ)*X 1 2) := by sorry
