-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302052_s6
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302052_s6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:17:21.995216+00:00
-- url     : https://prove2.me/theorems/7624dd4e-7424-4047-98a0-a7b356258055
-- title:
--   Hlawka collision chart 302053, bounded proof step 7
-- statement:
--   For the normalized ordered chart on $[65/16,67/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302052_s6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev5 : (0 : ℝ) ≤ ((3661/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3661/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3283/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3283/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1729/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1729/20000 : ℝ)*X 1 2)) : False := by sorry
