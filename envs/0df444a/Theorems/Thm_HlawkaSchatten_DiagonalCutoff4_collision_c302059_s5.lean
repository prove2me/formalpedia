-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302059_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302059_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:21:15.968137+00:00
-- url     : https://prove2.me/theorems/e5e863cd-5c2d-4bc1-96e8-da724ec7de6f
-- title:
--   Hlawka collision chart 302060, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[65/16,131/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302059_s5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((559/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(559/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53747/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53747/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11993/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11993/50000 : ℝ)*X 1 2)) : False := by sorry
