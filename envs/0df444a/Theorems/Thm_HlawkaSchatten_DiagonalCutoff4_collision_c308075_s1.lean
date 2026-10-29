-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308075_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c308075_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:25:02.353525+00:00
-- url     : https://prove2.me/theorems/367494c0-be61-4f7e-ae40-ca14da101870
-- title:
--   Hlawka collision chart 308076, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[17/4,69/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c308075_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((15991/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15991/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-18261/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-18261/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3419/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3419/4000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((56589/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(56589/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3113/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3113/4000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29201/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29201/50000 : ℝ)*X 1 2) := by sorry
