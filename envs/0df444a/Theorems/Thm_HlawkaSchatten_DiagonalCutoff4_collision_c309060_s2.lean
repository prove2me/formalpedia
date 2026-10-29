-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309060_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309060_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:41:59.371331+00:00
-- url     : https://prove2.me/theorems/271b2d90-123d-4048-a339-16f772718634
-- title:
--   Hlawka collision chart 309061, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309060_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((3201/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3201/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80603/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80603/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17471/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17471/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((60861/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60861/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15993/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15993/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23649/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23649/50000 : ℝ)*X 1 2) := by sorry
