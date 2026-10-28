-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s8
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301063_s8
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:40:51.514213+00:00
-- url     : https://prove2.me/theorems/20c8801c-ad59-4846-a1e3-ce167af701e2
-- title:
--   Hlawka collision chart 301064, bounded proof step 9
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301063_s8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev7 : (0 : ℝ) ≤ ((10009/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10009/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20277/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38663/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38663/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3839/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3839/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31007/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14821/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14821/50000 : ℝ)*X 1 2) := by sorry
