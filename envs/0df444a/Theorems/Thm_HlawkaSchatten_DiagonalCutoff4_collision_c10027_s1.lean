-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10027_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10027_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:11:05.718297+00:00
-- url     : https://prove2.me/theorems/a309cc41-5e3b-4b17-b47b-b591f9801def
-- title:
--   Hlawka collision chart 10028, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10027_s1 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((38587/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38587/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(83477/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(83477/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(8813/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(8813/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26497/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26497/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7439/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(7439/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(19431/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(19431/50000 : ℝ)*X 1 2) := by sorry
