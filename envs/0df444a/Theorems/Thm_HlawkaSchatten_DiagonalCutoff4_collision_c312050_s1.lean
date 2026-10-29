-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312050_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312050_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:19:07.467629+00:00
-- url     : https://prove2.me/theorems/93b87727-1feb-469d-b89e-8e93ca4f6ad5
-- title:
--   Hlawka collision chart 312051, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[9/2,37/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312050_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((21363/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21363/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7847/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7847/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-14499/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-14499/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1886/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1886/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6497/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6497/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-34609/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-34609/100000 : ℝ)*X 1 2) := by sorry
