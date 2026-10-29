-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310058_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310058_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:58:16.539565+00:00
-- url     : https://prove2.me/theorems/cfd60c4b-5a26-49b5-ab7a-6db1bb5be332
-- title:
--   Hlawka collision chart 310059, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[35/8,71/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310058_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((45039/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45039/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83299/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83299/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-9587/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-9587/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((72509/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72509/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65081/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(65081/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-43409/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-43409/100000 : ℝ)*X 1 2) := by sorry
