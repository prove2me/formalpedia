-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308053_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c308053_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:22:36.516981+00:00
-- url     : https://prove2.me/theorems/f70b22e2-04ca-43c2-bc20-365607e2b525
-- title:
--   Hlawka collision chart 308054, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[17/4,69/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c308053_s5 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((3939/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3939/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4577/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4577/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4401/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4401/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1793/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1793/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8851/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8851/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8779/50000 : ℝ)*X 1 2) := by sorry
