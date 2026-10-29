-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309054_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309054_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:41:07.863375+00:00
-- url     : https://prove2.me/theorems/92f15446-4f8e-4911-8478-9cd3a548b07c
-- title:
--   Hlawka collision chart 309055, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309054_s4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((851/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(851/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17823/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17823/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11611/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11611/50000 : ℝ)*X 1 2)) : False := by sorry
