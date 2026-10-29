-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c322053_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c322053_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:43:03.988754+00:00
-- url     : https://prove2.me/theorems/a9c40da5-dd0e-4b90-b540-d53ae43dc3ee
-- title:
--   Hlawka collision chart 322054, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[41/8,21/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c322053_s0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : (0 : ℝ) ≤ ((70597/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70597/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70657/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70657/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69197/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69197/100000 : ℝ)*X 1 2) := by sorry
