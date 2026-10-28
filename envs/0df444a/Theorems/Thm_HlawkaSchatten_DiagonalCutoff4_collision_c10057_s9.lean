-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10057_s9
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10057_s9
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:25:19.051935+00:00
-- url     : https://prove2.me/theorems/7ad71754-5e87-4819-85c1-d3ffc19b72c4
-- title:
--   Hlawka collision chart 10058, bounded proof step 10
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10057_s9 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev8 : (0 : ℝ) ≤ ((46223/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46223/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46223/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46223/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2339/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2339/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13899/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13899/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13899/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13899/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(433/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(433/10000 : ℝ)*X 1 2) := by sorry
