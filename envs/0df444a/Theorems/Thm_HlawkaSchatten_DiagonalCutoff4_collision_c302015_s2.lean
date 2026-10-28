-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302015_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302015_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:15:19.291208+00:00
-- url     : https://prove2.me/theorems/6c7b88ed-96fd-4cc7-945e-65e36819248e
-- title:
--   Hlawka collision chart 302016, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[65/16,67/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302015_s2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((53997/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(53997/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-41797/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-41797/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20741/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20741/50000 : ℝ)*X 1 2)) : False := by sorry
