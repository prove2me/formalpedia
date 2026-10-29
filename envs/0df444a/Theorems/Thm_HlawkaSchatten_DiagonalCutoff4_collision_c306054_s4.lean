-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306054_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c306054_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:35:48.705009+00:00
-- url     : https://prove2.me/theorems/ecd38718-9b77-4950-ba2b-b514b6becfdd
-- title:
--   Hlawka collision chart 306055, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[67/16,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c306054_s4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((52539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55307/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(55307/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-40081/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-40081/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33199/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33199/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17317/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11221/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11221/50000 : ℝ)*X 1 2) := by sorry
