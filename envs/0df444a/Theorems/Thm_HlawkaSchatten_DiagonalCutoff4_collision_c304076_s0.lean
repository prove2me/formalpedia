-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304076_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304076_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:36:57.164867+00:00
-- url     : https://prove2.me/theorems/a7244312-8b0c-4a0f-9b37-933ceda09624
-- title:
--   Hlawka collision chart 304077, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304076_s0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : (0 : ℝ) ≤ ((90189/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(90189/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-951/1000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-951/1000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48659/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48659/50000 : ℝ)*X 1 2) := by sorry
