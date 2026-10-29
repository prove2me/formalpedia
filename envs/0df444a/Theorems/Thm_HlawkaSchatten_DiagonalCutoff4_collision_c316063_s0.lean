-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316063_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c316063_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:16:03.528587+00:00
-- url     : https://prove2.me/theorems/99921f71-08a3-4d15-bbed-60165fe74ecf
-- title:
--   Hlawka collision chart 316064, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[19/4,77/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c316063_s0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((2444/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2444/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19463/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19463/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1889/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1889/2500 : ℝ)*X 1 2) := by sorry
