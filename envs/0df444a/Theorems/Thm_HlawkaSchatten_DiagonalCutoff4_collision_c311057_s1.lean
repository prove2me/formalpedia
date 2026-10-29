-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c311057_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c311057_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:07:03.350504+00:00
-- url     : https://prove2.me/theorems/13efd037-f31a-4992-b769-63a33ad78ef9
-- title:
--   Hlawka collision chart 311058, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[71/16,9/2]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c311057_s1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((4357/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4357/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21571/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21571/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(46901/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(46901/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2178/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2178/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6957/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6957/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18923/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18923/100000 : ℝ)*X 1 2) := by sorry
