-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308059_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c308059_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:24:07.558864+00:00
-- url     : https://prove2.me/theorems/4e91e3cf-da2b-47ca-a527-cb74d5bc6c5f
-- title:
--   Hlawka collision chart 308060, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[17/4,69/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c308059_s4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((23631/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23631/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45939/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45939/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(9299/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(9299/50000 : ℝ)*X 1 2)) : False := by sorry
