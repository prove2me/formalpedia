-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310055_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310055_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:57:17.438117+00:00
-- url     : https://prove2.me/theorems/5a9f94fc-0b8d-40f1-a05c-6334b7d47d74
-- title:
--   Hlawka collision chart 310056, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[35/8,71/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310055_s4 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((1326/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1326/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43261/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43261/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5321/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5321/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6871/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6871/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13461/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13461/50000 : ℝ)*X 1 2) := by sorry
