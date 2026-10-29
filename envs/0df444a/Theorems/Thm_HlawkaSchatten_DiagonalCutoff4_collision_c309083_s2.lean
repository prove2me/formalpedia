-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309083_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309083_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:43:45.024969+00:00
-- url     : https://prove2.me/theorems/7f62ddd5-8936-4c58-a67b-cdf1cd496e1a
-- title:
--   Hlawka collision chart 309084, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309083_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((58687/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58687/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((56283/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(56283/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2067/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2067/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((859/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(859/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((29973/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(29973/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1509/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1509/5000 : ℝ)*X 1 2) := by sorry
