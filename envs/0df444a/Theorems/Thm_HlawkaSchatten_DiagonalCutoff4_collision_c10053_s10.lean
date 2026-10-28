-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10053_s10
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10053_s10
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:20:15.333792+00:00
-- url     : https://prove2.me/theorems/c53b6318-a2df-44d9-8a7a-e2bc0e633ed4
-- title:
--   Hlawka collision chart 10054, bounded proof step 11
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10053_s10 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev9 : (0 : ℝ) ≤ ((6047/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6047/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34673/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34673/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8359/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8359/25000 : ℝ)*X 1 2)) : False := by sorry
