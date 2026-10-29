-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314031_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c314031_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:59:05.119983+00:00
-- url     : https://prove2.me/theorems/4c00c1ff-9c51-4b66-a402-6fc3156cb802
-- title:
--   Hlawka collision chart 314032, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[37/8,19/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c314031_s0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((36001/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36001/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(56771/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(56771/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79153/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79153/100000 : ℝ)*X 1 2) := by sorry
