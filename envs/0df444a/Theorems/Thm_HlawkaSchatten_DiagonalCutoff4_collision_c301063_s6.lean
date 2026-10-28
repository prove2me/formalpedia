-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s6
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301063_s6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:40:41.990978+00:00
-- url     : https://prove2.me/theorems/be8e1542-6a52-45f5-a77e-8a43794afbc6
-- title:
--   Hlawka collision chart 301064, bounded proof step 7
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301063_s6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((1998/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1998/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64669/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64669/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31007/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13117/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13117/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53323/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53323/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12739/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12739/25000 : ℝ)*X 1 2) := by sorry
